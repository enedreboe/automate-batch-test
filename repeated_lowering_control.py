# -*- coding: utf-8 -*-
_VERSION = 'Version 1.31 - 10 Aug 2016'
"""
--- Description ---
This script will control the throughput of the files running in the automated batch.
The inputs should come as arguments (defined in master_script.py). See the definition of the
function run for a detailed list of the required input arguments.

The simulations are run using the 'checkMissingResultsandResubmit.py' script, which first checks
if the results files are available. Therefore if the script stops for some reason, you just need
to re-start it and it will not need to re-run the Hs already done, it will see that the results
are there and just post-process them.

This is also valid for changes in the post-processing. Say there was a mistake in the limiting
variables, you can just update it and re-run the script, without deleting the batch files. So the
script will only post-process without re-running all the simulations. Logically any extra failing
Tp not detected before will need re-run.

For changes in the model, hence requiring a full re-run of the cases, you'll need to delete all
the previous files.

Simulations are run in multiple-passes runs: start with large Hs and a full range of Tps. After
checking the limiting criteria, re-runs the non-acceptable Tps for lower Hs in a defined Hs step.
When all Tps are acceptable, or Hs reaches 1m, the script chooses a better starting point for Hs
and a smaller Hs step and re-run the script. In order to keep the passes efficent, it is important
that the Hs steps are multiple of each other, e.g. [0.4, 0.2, 0.1], [0.5, 0.25]. You can however
have any value you want for the steps, and any number of steps.

IMPORTANT: when re-running batches, the existing YML files are not overwriten, but the results
files are. So if you've changed something in the model, please delete the YML files yourself
before running this script.

"""
import os
import sys
import time
# import tempfile
import GumbelFit_opt as GumbelFit
import preProcessing
import CombineResults
import checkMissingResultsandResubmit
from math import sqrt, exp
import postProcessing_py as postProcessing
import create_results_xl
# %%


class WeatherWindow():
    """Class WeatherWindow: repesents the allowable, not-allowable and not applicable sea states
    from the lifting analysis.

    A table Hs\Tp is built, initially with all sea states marked as 'run' or 'na', which means
    that they need to be simulated or are not applicable, respectively.

    Not applicable sea states are periods out of the range for a given Hs, low period and large Hs.

    As the simulations are run, for each Hs that is finished, the table is updated with the
    not-acceptable and acceptable Tps, marked as 'no' and 'ok' respectively.

    These results are propagated for others Hs in the table. Acceptable periods are propagated to
    lower Hs whilst not-acceptable periods are propagated to higher Hs.

    This, together with the simulations run with multiple Hs_steps, allows for a quick screening
    of cases that don't need to be run.

    Init
    ----
    WeatherWindow (hs_start, hs_steps, tp_start, tp_end, tp_step)
        initialises the weather window table for the range of Hs and Tp as per input. Minimum
        Hs is assumed to be 1m.

    Variables
    ---------
    table
        dictionary of dictionaries, use table[hs][tp] will be 'na', 'run', 'ok' or 'no'
    hs_table
        simplified dictionary with max allowable Hs per Tp: {tp1: hs1, tp2: hs2, ...}
    Hss
        Private. List of all Hs values in the table, descending order.
    Tps
        Private. List of all Tp values in the table, ascending order.

    Public Methods
    --------------
    update (hs, not_acceptable_tps)
        Updates the weather window table for a given Hs with the not acceptable Tps for that Hs.
        Also calls update_hs_table ().
    get_tps2run (hs)
        Returns a list of Tps that need to be simulated for that Hs, empty list if none.
    get_next_hs_start ()
        Returns the highest Hs with at least one sea state marked as 'run'.
    is_run_complete ()
        Returns True if all sea states have been marked as 'ok', 'no', or '.'.
        Returns False is any sea state is still marked as 'run', i.e, simulations for that sea
        state have not run yet and results cannot be derived from other sea states.
    print_full_table (filename=None, timestamp=False)
        Simple text output to screen and optionally to file of the weather window table. Used in
        the script to report progress.
    print_simple_table (filename=None, timestamp=False, toscreen=True)
        Print a 2-line table with Tp and limiting Hs.
        filename: if given, appends also to file.
        timestamp: if set to True, adds a timestamp at the start of the line.
        toscreen: if set to true, shows output in the screen.
    print_window(summary_file_wwindow, logfile)
        Prints a text version of the allowable weather window, with all Hss and Tps from the
        simulations and allowed, not allowed and not applicable sea states marked as 'ok', 'no'
        and '-' respectively. Output is shown in screen and saved to logfile and to summary file.

    Private Methods
    ---------------
    hs_range (start, end, step)
        Returns a list of Hs, from start to en including end, at a given step. Descending order.
    update_hs_table ()
        Updates hs_table (see definition above). Called after initi and by update().

    """
    def __init__(self, hs_start, hs_steps, hs_min,
                 tp_start, tp_end, tp_step_low, tp_step_high, tp_step_change, tp_extra):
        self.table = dict()
        self.hs_table = dict()
        self.tp_start = tp_start
        self.hs_start = hs_start
        self.hs_min = hs_min

        # create list of Hs in _descending_ order! don't change!
        hss = set()
        for delta in hs_steps:  # hs list has to cover all hs_steps
            hss = hss.union(set(self.hs_range(hs_start, hs_min, -delta)))
        self.Hss = list(hss)
        self.Hss.sort()
        self.Hss.reverse()

        # list of Tps in _ascending_ order
        self.Tps = self.tp_range(tp_start(hs_min), tp_end, tp_step_low,
                                 tp_step_high, tp_step_change)

        # manually add user selected Tps
        for tp in tp_extra: self.Tps.append(tp)
        self.Tps = list(set(self.Tps))
        self.Tps.sort()

        # initialise weather window table with 'run' and 'na'
        for hs in self.Hss:
            self.table[round(hs, 3)] = dict()
            for tp in self.Tps:
                if tp < tp_start(hs):
                    self.table[round(hs, 3)][round(tp, 3)] = 'na'
                else:
                    self.table[round(hs, 3)][round(tp, 3)] = 'run'
        self.update_hs_table()

    def hs_range(self, start, end, step):
        """Returns a list from start to and including end. Accepts floats."""
        x = [round(start, 3)]
        while x[-1] >= round(end-step, 3):
                x.append(round(x[-1]+step, 3))
        return x

    def tp_range(self, start, end, step_low, step_high, change):
        """Returns a list from start to and including end. Accepts floats.
        The increments for tp is step_low to tp <= change and step_high otherwise.
        In case start > change, step_low is used. In case end < change, step_high is used.
        """
        tps = [round(start, 3)]
        while tps[-1] <= round(min(change, end)-step_low, 3):
            tps.append(round(tps[-1]+step_low, 3))
        while tps[-1] <= round(end-step_high, 3):
            tps.append(round(tps[-1]+step_high, 3))
        return tps

    def update(self, hs, run_Tps, not_acceptable_tps):
        """When one Hs is run, the results are used to update the weather window.
        All green Tps for this Hs are also assumed green for LOWER Hss.
        All red Tps for this Hs are also assumed red for HIGHER Hss.
        """
        hs = round(hs, 3)
        for hs_i in self.table.keys():
            # mark lower hs with 'ok'
            if hs_i <= hs:
                for tp in run_Tps:
                    if tp not in not_acceptable_tps and self.table[hs_i][round(tp, 3)] == 'run':
                        if tp >= self.tp_start(hs):
                            self.table[hs_i][round(tp, 3)] = 'ok'
            # mark higher hs with 'not ok'
            if hs_i >= hs:
                for tp in not_acceptable_tps:
                    self.table[hs_i][round(tp, 3)] = 'no'
        self.update_hs_table()

    def update_hs_table(self):
        """Updates the dictionaty with the maximum allowed Hs per Tp:
        {tp1: max_hs1, tp2: max_hs2, ...}
        """
        for tp in self.Tps:
            for hs in self.Hss:  # hs in desceding order
                if self.table[round(hs, 3)][round(tp, 3)] == 'ok':
                    self.hs_table[round(tp, 3)] = hs
                    break
            else:  # fill in zero in case no window found for all Hs
                self.hs_table[round(tp, 3)] = 0.0

    def get_tps2run(self, hs):
        """Returns the Tps that need to be run for a given Hs."""
        hs = round(hs, 3)
        tps2run = [round(tp, 3) for tp in self.table[hs].keys() if self.table[hs][tp] == 'run']
        tps2run.sort()
        return tps2run

    def get_next_hs_start(self, hs_step):
        """Returns the largest Hs respecting hs_step with Tps still marked as 'run'"""
        # Hss has to be in descending order for this to work!
        hss = self.hs_range(self.hs_start, self.hs_min, -hs_step)
        for hs in hss:
            if 'run' in self.table[round(hs, 3)].values():
                return hs
        return False

    def is_run_complete(self):
        """Returns false if table doesn't contain any 'run' entry, otherwise returns True"""
        if 'run' in {v for k in self.table.keys() for v in self.table[k].values()}:
            return False
        else:
            return True

    def print_full_table(self, filename=None, timestamp=False):
        """Prints the full weather window table during running of script, including
        'na', 'run', 'ok' and 'no'. This is used in the end of every inner-step to show
        progress and cases still to be run.
        """
        outs = [sys.stdout]
        if filename: outs.append(open(filename, 'a'))
        for k, obj in enumerate(outs):
            obj.write(timest(timestamp) + 'Progress:\n')
            obj.write(timest(timestamp) + '    Hs\Tp ')
            for tp in self.Tps:
                obj.write('%5.2f ' % tp)
            obj.write('\n')
            for hs in self.Hss:
                obj.write(timest(timestamp) + '    %5.2f ' % hs)
                for tp in self.Tps:
                    obj.write('%5s ' % self.table[round(hs, 3)][round(tp, 3)])
                obj.write('\n')
            if k > 0:
                obj.flush()
                obj.close()

    def print_simple_table(self, filename=None, timestamp=False, toscreen=True):
        """Prints out a summary of the weather window, with the maximum allowed Hs per Tp.
        To be used with the output create_hsd_table(): print_hsd_table(create_hsd_table(...))
        If filename is given, also prints to file. A timestamp is optionally also printed out.
        """
        outs = []
        if toscreen: outs.append(sys.stdout)
        if filename: outs.append(open(filename, 'a'))
        for obj in outs:
            obj.write(timest(timestamp) + 'Maximum allowable design Hs per Tp:\n')
            obj.write(timest(timestamp) + 'Tp [s]:')
            for tp in self.Tps: obj.write(' %5.2f' % tp)
            obj.write('\n')
            obj.write(timest(timestamp) + 'Hs [m]:')
            for tp in self.Tps: obj.write(' %5.2f' % self.hs_table[tp])
            obj.write('\n')
        idx = 0
        if toscreen: idx = 1
        if filename: outs[idx].close()

    def print_window(self, summary_file_wwindow, logfile):
        """Prints out a table Hs/Tp with acceptable, non-acceptable and non-applicable sea states
        If filename is given, prints to file. A timestamp is optionally also printed out.
        """
        outs = [sys.stdout, open(logfile, 'a'), open(summary_file_wwindow, 'a')]
        for k, obj in enumerate(outs):
            timestamp = True if k < 2 else False  # only in stdout and logfile
            obj.write(timest(timestamp) + 'Allowable Weather Window - Design Hs x Tp\n')
            obj.write(timest(timestamp) + '    Hs\Tp')
            for tp in self.Tps: obj.write(' %5.2f' % tp)
            hss = self.Hss.copy()
            hss.reverse()  # here we want ascending order
            for hs in hss:
                obj.write('\n' + timest(timestamp) + '    %.2f' % hs)
                for i, tp in enumerate(self.Tps):
                    if tp < self.tp_start(hs):
                        obj.write('    - ')
                    elif hs <= self.hs_table[tp]:
                        obj.write('    ok')
                    else:
                        obj.write('    no')
            obj.write('\n')
            if k > 0:
                obj.flush()
                obj.close()
# %%


def tp_start_DNVH103(hs, alpha_factor=0.95):
    """Start Tp per Hs - JONSWAP spectrum.
    Returns the starting Tp as recommended by DNV-RP-H103 and OS-C205.
    Gamma is assumed 5 - which is the case for low Tp.
    Tp is rounded to the closest integer.
    Alpha factor taken as input to ensure worst Hs is captured. Default value 0.95.
    """
    if hs < 0.1: return 1.0
    return round(11*sqrt(hs*alpha_factor/9.8), 0)


def jonswap_gamma_DNVH103(hs, tp):
    """JONSWAP gamma as per DNV-H103"""
    if hs < 0.1: return 1.0
    alpha = tp/sqrt(hs)
    if alpha >= 3.6 and alpha <= 5.0:
        return exp(5.75-1.15*alpha)
    if alpha < 3.6:
        return 5.0
    if alpha > 5.0:
        return 1.0


def timest(flag):
    """string with time stamp"""
    if flag:
        return '[%s] ' % time.asctime()
    else:
        return ''


def estimate_time(fname_missing='missing.txt', frequency='default'):
    """Very simple function to estimate when to check again if the cases are finished in DOF.
    Reads how many cases to run from missing.txt.
    """
    try:
        n_cases = sum(1 for line in open(fname_missing))
    except:
        n_cases = 0
    if frequency == 'fast':
        if n_cases > 100:
            return n_cases, round(n_cases/100)*30+30
        return n_cases, 15
    elif frequency == 'slow':
        if n_cases > 50:
            return n_cases, round(n_cases/50)*150+60
        return n_cases, round(n_cases/50)*60+30
    else:  # frequency == 'default':
        if n_cases > 100:
            return n_cases, round(n_cases/50)*150+60
        return n_cases, round(n_cases/50)*60+30


def strtimes(seconds):
    """Returns a read-friendly string for time input in seconds."""
    if seconds < 60:
        return '%ds' % seconds
    minutes, seconds = int(seconds/60), seconds % 60
    if minutes < 60:
        return '%dm:%ds' % (minutes, seconds)
    hours, minutes = int(minutes/60), minutes % 60
    if hours < 24:
        return '%dh:%dm' % (hours, minutes)
    days, hours = int(hours/24), hours % 24
    return '%dd:%dh' % (days, hours)


def fname_pattern(hs, tp, wd, seed_idx):
    """pattern used to create YML files and read results TXT files"""
    return 'Hs%.2f_Tp%05.2f_WD%d_seed%d' % (hs, tp, wd, seed_idx)


def log(string, filename=None, timestamp=False):
    """Prints a string to screen. If filename is given, prints also to file.
    To give feedback messages about batch progress, use this function
    instead of a normal print function.
    A timestamp is optionally printed out.
    """
    outs = [sys.stdout]
    if filename: outs.append(open(filename, 'a'))
    for obj in outs:
        obj.write(timest(timestamp) + string)
    if filename:
        outs[1].flush()
        outs[1].close()


def summary_loads(gumbel_sum_res, vars_limits, useMLE, w_window, logfile, wwindow_file):
    """Reads the static loads from a file, summarise the dynamic loads from the pandas panel from
    the gumbel script, saves a summary of the static and dynamic loads to a text file and
    return a list with the static loads.
    """
    # Read and save static loads
    log('Reading static results.\n', logfile, True)
    try:
        with open('runs\\static.txt', 'r') as f:
            tmp = f.readlines()
        # Remove final \n, split at tabs and get rid of Hs, Tp and wdir:
        headers = [x for x in tmp[0][:-1].split('\t')[3:]]
        static_loads = [float(x) for x in tmp[1][:-1].split('\t')[3:]]
    except FileNotFoundError:
        log('!!! Warning:\n', logfile, True)
        log('!!! File "runs\\static.txt" not found. Static case still running?\n', logfile, True)
        log('!!! If yes, wait until it is finished and re-run this script.\n', logfile, True)
        log('!!! For now, the static loads will be set to zero.\n', logfile, True)
        log('!!!\n', logfile, True)
        static_loads = [0] * len(vars_limits)
        headers = [v[0] for v in vars_limits]
        # raise SystemExit

    # Now need to do some checking here since the variables asked in PostCalcActions.py might
    # differ from vars_limits - PostCalcActions can have *more* entries than vars_limits.
    # headers and static_loads defined above come from PostCalcActions. Need to filter and leave
    # only entries present in vars_limits:
    vars_names = [x[0] for x in vars_limits]
    idx2del = []
    for i, h in enumerate(headers):
        if h not in vars_names:
            idx2del.append(i)
    idx2del.reverse()
    for i in idx2del:
        headers.remove(headers[i])
        static_loads.remove(static_loads[i])

    # A summary of the max/min loads only for acceptable sea states
    log('Summarising dynamic loads.\n', logfile, True)

    # Initialise extremes with dummy lagr value
    dummy_extreme = 999999999
    extremes = dict()
    for var in vars_limits:
        name = var[0] + ' ' + str(var[1])
        if name.lower().find('max') > 0:
            extremes[name] = -dummy_extreme
        else:  # min
            extremes[name] = dummy_extreme

    if useMLE:
        method = 'MLE and sample'
    else:
        method = 'ME and sample'
    data = gumbel_sum_res[method]

    # when using data[...].min(), only numbers are accepted, so any
    # columns with not-numbers will raise an error. this may happen in the minimum values since
    # Gumbel fit is not performed with zeros in the sample, and in this case, if not enough
    # seeds has been run, a string will be places at that entry:
    str_moreseeds = 'need to run more seeds for this confidence level'
    min_moreseeds = -99999.99
    data = data.replace(to_replace=str_moreseeds, value=min_moreseeds)

    # Loop though all sea states
    for tp in w_window.Tps:
        # Note that Hss is in descending order
        for hs in w_window.Hss:
            # Acceptable sea states
            # Note that extremes will only be filled in with proper values if there is an allowable
            # window somewhere, otherwise extremes will have dummy_extreme
            if w_window.table[hs][tp] == 'ok':
                for var in vars_limits:
                    name = var[0]  # name of the variable
                    p = var[1]     # probability of non-exceedance
                    e = ' ' + str(p)  # var name in pandas doesnt have probability.
                    if name.lower().find('max') > 0:  # find maxima
                        extremes[name+e] = max(extremes[name+e],
                                               data[(data['Hs'] == hs) & (data['Tp'] == tp) &
                                               (data['Confidence level'] == p)][name].max())
                    else:
                        extremes[name+e] = min(extremes[name+e],
                                               data[(data['Hs'] == hs) & (data['Tp'] == tp) &
                                               (data['Confidence level'] == p)][name].min())
                # Skip smaller Hss
                break

    # ok, this is becoming a bit messy: static loads don't depend on confidence level, but
    # the maximum dynamic loads do. So, above, headers and var_names only has the name of the
    # variable, without p, for example, 'Winch Max Tension'. BUT in the summary of loads,
    # since the dynamic loads are given, we do want the p to be present, such that if the
    # user requests the same variable for different p's, the same static load will be reported,
    # but with different percentile, for example 'Winch Max Tension 0.9', and '... 0.99'.
    vars_names_w_p = [x[0]+' '+str(x[1]) for x in vars_limits]
    dict_static_loads = dict()
    for i, h in enumerate(headers):
        dict_static_loads[h] = static_loads[i]

    with open('Static_and_Characteristic_loads.txt', 'w') as f:
        for s in vars_names_w_p:
            f.write('%s\t' % s)
        f.write('\n')
        for s in vars_names:
            f.write('%f\t' % dict_static_loads[s])
        f.write('\n')
        for h in vars_names_w_p:
            if round(extremes[h], 2) == round(min_moreseeds, 2):
                f.write('%s\t' % 'not enough seeds')
            elif round(abs(extremes[h]), 2) == round(dummy_extreme, 2):
                f.write('%s\t' % 'no window')
            else:
                f.write('%f\t' % extremes[h])

    # Puts a summary of load in screen
    outs = [sys.stdout, open(logfile, 'a'), open(wwindow_file, 'a')]

    for k, obj in enumerate(outs):
        timestamp = True if k < 2 else False
        obj.write(timest(timestamp) + 'Summary of static and characteristic loads:\n')
        width = max([len(x[0]) for x in vars_limits]) + 4
        obj.write(timest(timestamp) + '%*s\t%8s\t%8s\n' % (width, 'Variable',
                                                               'Static', 'Dynamic'))
        for i, var in enumerate(vars_names_w_p):
            if round(extremes[var], 2) == round(min_moreseeds, 2):
                str_extr = 'not enough seeds'
            elif round(abs(extremes[var]), 2) == round(dummy_extreme, 2):
                str_extr = 'no window'
            else:
                str_extr = '%8.2f' % extremes[var]
            obj.write(timest(timestamp) + '%*s\t%8.2f\t%s\n' % (
                      width, var, dict_static_loads[vars_names[i]], str_extr))

        if k > 0:
            obj.flush()
            obj.close()

    # This will repeat any static load for variables asked with more than 1 percentile:
    static_loads = [dict_static_loads[name] for name in vars_names]

    return static_loads


def create_gumbel_plots(gumbel_res, gumbel_sum_res, vars_limits, useMLE, w_window, num_of_seeds,
                        confidence_level, concat_results_file, logfile):
    """Create Gumbel plots for limiting sea states. For each Tp, only plots limiting Hs to avoid
    creating too many plot, plotting function to be called directly from gumbel module.
    To do that, some other variables are extracted here.
    """
    log('Creating Gumbel plots for limiting sea states.\n', logfile, True)
    sample, num_row_sample, num_col_sample = GumbelFit.readResultFile(concat_results_file)
    colnames = [_ for _ in range(int(num_row_sample/num_of_seeds))]

    if useMLE:
        method = 'MLE and sample'
    else:
        method = 'ME and sample'
    tps = list(w_window.hs_table.keys())
    tps.sort()
    for tp in tps:
        hs_lim = w_window.hs_table[round(tp, 3)]  # limiting Hs per Tp
        log('Gumbel plot for Tp %.2fs, Hs %.2fm.\n' % (tp, hs_lim), logfile, True)

        # filter the full results dataframe into smaller sets
        res_tmp = gumbel_sum_res[method][gumbel_sum_res[method]['Tp'] == round(tp, 3)]
        res_tmp = res_tmp[res_tmp['Hs'] == hs_lim]

        for var, conf, lim in vars_limits:
            # ires only has 1 entry per wave heading
            ires = res_tmp[res_tmp['Confidence level'] == conf]

            # gets the wave direction, wd, with the worst results
            # only this wd will be plotted.
            try:
                if var.lower().find('min') > 0:
                    wd = ires['WaveDir'][ires[var].argmin()]
                else:
                    wd = ires['WaveDir'][ires[var].argmax()]
            except:
                # if sample has 'need to run more seeds', .argmin() will raise an error
                log('Skipped %s - need more seeds.\n' % var, logfile, True)
                continue

            GumbelFit.plotProbability(gumbel_res, sample, colnames, num_of_seeds, confidence_level,
                                      Objectplot=[var],
                                      PlotWd=[wd],
                                      PlotHs=[hs_lim],
                                      PlotT=[tp])
    log('Gumbel plots created in sub-directory Plots.\n', logfile, True)


def copy_postcalc(model_file_name, logfile):
    """Copies the post calculation actions script(s) into the subfolder 'runs'
    Also creates a post calc action which will serve as progress identifier.
    """
    try:
        from OrcFxAPI import Model as ofModel
        from shutil import copy2
    except:
        log('Warning: Not able to load OrcFxAPI.\n', logfile, True)
        log('Please copy post calc script manually into the runs folder.\n', logfile, True)
        return False

    if not os.path.exists('runs'):
        os.mkdir('runs')

    log('Reading name of post calculation actions scripts from model.\n', logfile, True)
    m = ofModel(model_file_name)

    # Names of extra post calc action to report batch progress
    progactionname = 'Progress'
    progscriptname = 'PostCalcActionProgress.py'

    # Copy post calc action scripts into sub directory runs
    for i in range(m.general.GetData('NumberOfPostCalculationActions', 0)):
        m.general.SelectedPostCalculationAction = m.general.GetData('PostCalculationActionName', i)
        postcalc_name = m.general.GetData('PostCalculationActionScriptFileName', 0)
        if not postcalc_name == progscriptname:
            log('Copying %s into folder runs.\n' % postcalc_name, logfile, True)
            copy2(postcalc_name, 'runs')

    # Set up model for the progress post calc action
    log('Setting up extra post calc action to report batch progress.\n', logfile, True)
    if not m.general.SelectedPostCalculationAction == progactionname:
        #
        m.general.SetData('NumberOfPostCalculationActions', 0, i+2)
        m.general.SetData('PostCalculationActionName', i+1, progactionname)
        m.general.SelectedPostCalculationAction = progactionname
        m.general.SetData('PostCalculationActionPythonVersion', 0, 'Python 3')
        m.general.SetData('PostCalculationActionScriptFileName', 0, progscriptname)
        m.SaveData(model_file_name)

    # Creates the progress post calc script in sub directory runs
    log('Creating post calc script to report progress.\n', logfile, True)
    with open('runs\\' + progscriptname, 'w') as f:
        f.write("import os.path\n\n\n")
        f.write("def Execute(info):\n")
        f.write("    info.model.ReportActionProgress('Writting progress file')\n")
        # Note: the dir name __prog__ is also hardcoded in chkmissing.findMissingFiles() !
        f.write("    progdir = os.path.join(info.modelDirectory, '__prog__')\n")
        f.write("    if not os.path.exists(progdir):\n")
        f.write("        os.mkdir(progdir)\n")
        f.write("    outputFileName = os.path.splitext(os.path.basename(info.modelFileName))[0]\n")
        f.write("    with open(os.path.join(progdir, outputFileName+'.prog'), 'w') as f:\n")
        f.write("        f.write('Done.\\n')\n")
        f.write("    return None\n")

    return True


def print_header(model_file_name, vars_limits, info_header, hs_start, hs_steps, hs_min,
                 jonswap_gamma, seeds, seed_random_generator, confidence_level,
                 tp_start, tp_end, tp_step_low, tp_step_high, tp_step_change,
                 wave_dirs, useMLE, concat_results_file, summary_file_loads,
                 summary_file_statistical, summary_file_wwindow, logfile):
    """Prints a short header of the job running. If filename is given, prints to file"""
    outs = [sys.stdout, open(logfile, 'w'), open(summary_file_wwindow, 'w')]
    for i, obj in enumerate(outs):
        obj.write('Script version: %s\n' % _VERSION)
        obj.write('\nInput data\n%s\n' % ('='*97))
        obj.write(info_header+'\n')
        obj.write('Orcaflex model: %s\n' % model_file_name)
        obj.write('Limiting Criteria:\n')
        width = max([len(x[0]) for x in vars_limits]) + 4
        obj.write('%*s\t%6s\t%8s\n' % (width, 'Variable', 'Conf', 'Limit'))
        for var, c, x in vars_limits:
            obj.write('%*s\t%.4f\t%8.2f\n' % (width, var, c, x))
        obj.write('\nStart Hs [m]                      : %.2f\n' % hs_start)
        obj.write('Steps Hs [m]                      :')
        for st in hs_steps: obj.write(' %.2f' % st)
        obj.write('\n')
        obj.write('Minimum Hs [m]                    : %.2f\n' % hs_min)
        obj.write('Start Tp                          ')
        if tp_start == tp_start_DNVH103:
            obj.write(': as per DNV-RP-H103\n')
        else:
            obj.write(': user defined\n')
        obj.write('End Tp [s]                        : %.2f\n' % tp_end)
        obj.write('Step Tp for low Tps[s]            : %.2f\n' % tp_step_low)
        obj.write('Step Tp for high Tps[s]           : %.2f\n' % tp_step_high)
        obj.write('Tp to change step [s]             : %.2f\n' % tp_step_change)
        obj.write('Wave directions                   :')
        for wd in wave_dirs: obj.write(' %d' % wd)
        obj.write('\n')
        obj.write('Confidence levels                 :')
        for c in confidence_level: obj.write(' %.4f' % c)
        obj.write('\n')
        if isinstance(seeds, int) or isinstance(seeds, float):
            obj.write('Number of seeds                   : %d - randomly generated\n' % seeds)
            obj.write('Initial state for random generator: %s\n' % seed_random_generator)
        else:
            obj.write('Number of seeds                   : %d - user defined\n' % len(seeds))
            for s in seeds: obj.write('\t%d\n' % s)
        obj.write('Gumbel fit method                 : ')
        if useMLE: obj.write('MLE (maximum likelihood estimators)\n')
        else: obj.write('ME (moments estimators)\n')
        obj.write('Concatenated batch results file   : %s\n' % concat_results_file)
        obj.write('Summary results with loads        : %s\n' % summary_file_loads)
        obj.write('Summary statistical results       : %s\n' % summary_file_statistical)
        obj.write('Summary weather window            : %s\n' % summary_file_wwindow)
        obj.write('Script run logged in              : %s\n' % logfile)
        obj.write('\n')
        if i > 0:
            obj.flush()
            obj.close()


def run(model_file_name, vars_limits, info_header,
        hs_start=3.5,
        hs_steps=[0.4, 0.2],
        hs_min=1.0,
        jonswap_gamma=jonswap_gamma_DNVH103,
        seeds=50,
        seed_random_generator=12343,
        tp_start=tp_start_DNVH103,
        tp_end=14,
        tp_step=1,
        tp_step2=1,
        tp_step_change=8,
        tp_extra=[],
        wave_dirs=[165, 180, 195],
        useMLE=True,
        plot=True,
        concat_results_file='Results.txt',
        summary_file_loads='Summary of predicted max_min loads.xlsx',
        summary_file_statistical='Statistical results.xlsx',
        summary_file_wwindow='Weather Window.txt',
        logfile='batch_log.txt',
        simtime_estimate='default'
        ):
    """Main function to run the simulations and iterate through Hs and Tp to find limiting Hs.

    Non-optional arguments
    ----------------------
        model_file_name
            name of the orcaflex model file
        vars_limits
            list with the limitations of the variables
        info_header
            header text containing project information

    Remarks on some _optional_ arguments
    ------------------------------------
        jonswap_gamma
            function of hs and tp, returning value of gamma. Default is as per DNV-H103.
            To skip setting gamma in the yml files, set it to False.
        tp_start
            Can be a function of hs or a number, returning the starting tp. Default is a
            function as per DNV-H103.
        seeds
            Can be a number (number of seeds) or an iterable object with the user defined seeds.
            Default is 50. The iterable object can be a list, tuple, set, generator, numpy.array.
            If a number is given, the seed values will be generated randomly.
        seed_random_generator
            Can be any hashable object. Only used if seeds is a number. Sets the
            initial state of the seed random generator.
        simtime_estimate
            'default', 'fast', 'slow'
    """

    # seeds can be either a number (default) or an iterable
    if isinstance(seeds, int) or isinstance(seeds, float):
        num_of_seeds = seeds
    elif hasattr(seeds, '__iter__'):
        num_of_seeds = len(seeds)

    # start_tp can be either a function of Hs (default) or a number
    if isinstance(tp_start, int) or isinstance(tp_start, float):
        tp_start_num = tp_start
        tp_start = lambda hs: tp_start_num

    # handles the error of tp_extra passed as a number rather than as an iterable
    if isinstance(tp_extra, int) or isinstance(tp_extra, float):
        tp_extra = [tp_extra]

    # handles the error of hs_steps passed as a number rather than as an iterable
    if isinstance(hs_steps, int) or isinstance(hs_steps, float):
        hs_steps = [hs_steps]

    # handles the error of hs_ or tp_step being zero, which would lead to a deadlock
    if 0 in hs_steps:
        log('ERROR: hs_steps must not be zero.\n')
        raise SystemExit
    if tp_step == 0 or tp_step2 == 0:
        log('ERROR: tp_step and tp_step2 must not be zero.\n')
        raise SystemExit

    # handles the error of hs_min being < zero
    if hs_min <= 0:
        log('ERROR: hs_min must not be zero.\n')
        raise SystemExit

    # reads confidence levels from vars_limits
    confidence_level = set()
    for _, c, _ in vars_limits: confidence_level.add(c)
    confidence_level = list(confidence_level)
    confidence_level.sort()

    log('Repeated Lowering - Automated Batch\n')
    print_header(model_file_name, vars_limits, info_header, hs_start, hs_steps, hs_min,
                 jonswap_gamma, seeds, seed_random_generator, confidence_level,
                 tp_start, tp_end, tp_step, tp_step2, tp_step_change,
                 wave_dirs, useMLE, concat_results_file, summary_file_loads,
                 summary_file_statistical, summary_file_wwindow, logfile)

    log('Please report any errors or comments to rarossi@technip.com\n\n', logfile)
    log('Starting analysis\n%s\n\n' % ('='*97), logfile)

    # copy post calculation actions script into the subfolder runs
    # also set up the model to have a final post calc action to mark progress
    # this required OrcFxAPI. If not available, switch back to old approach.
    if copy_postcalc(model_file_name, logfile):
        progress_approach = 'prog'
    else:
        progress_approach = 'old'

    allowable_weather_window = dict()
    w_window = WeatherWindow(hs_start, hs_steps, hs_min,
                             tp_start, tp_end, tp_step, tp_step2, tp_step_change, tp_extra)

# The below was though for a better handling of the file missing.txt, ussing a unique name instead.
# This would allow for more than 1 script run in parallel in the same directory.
#
#    # create sub-directory runs it doesn't exist
#    if not os.path.exists('runs'):
#        os.mkdir('runs')
#
#    # creates a unique filename to be used for missing.txt
#    pf = tempfile.NamedTemporaryFile(mode='w', dir='.\\runs', prefix='missing_',
#                                     suffix='.txt', delete=True)
#    pf.close()
#    fname_missing = pf.name
    fname_missing = 'missing.txt'

    # %%
    # STATIC CASE
    # Create a static case named 'static.yml'
    log('Creating a static case - without waves\n', logfile, True)
    preProcessing.main(hs=0.0, Tps=[1.0], wave_dirs=[180.0], BaseFile=model_file_name,
                       fname_pattern=lambda *args: 'static', seeds=[1])
    # Run it
    if os.path.exists('runs\\static.txt'):
        log('Static case alreayd run.\n', logfile, True)
    else:
        log('Sending the static case to DOF\n', logfile, True)
        os.chdir('runs')  # folder 'runs' is created in preProcessing
        with open(fname_missing, 'w') as f:
            f.write('static.yml\n')
        checkMissingResultsandResubmit.resubmitToDOF(fname_missing)
        os.chdir('..')  # folder 'runs' is created in preProcessing

    # %%
    # Main loop
    hs_steps.sort()     # just to make sure
    hs_steps.reverse()  # you never know =)
    # sea_states for post-processing, which will differ from the sea_states to be run
    sea_states_2post = dict()
    for hs_step in hs_steps:
        hs_start = w_window.get_next_hs_start(hs_step)  # update starting point for hs
        if not hs_start:
            break
        hs = hs_start
        Tps = w_window.get_tps2run(hs)
        if not Tps:
            break
        log('========================= Hs steps of %.2f m =========================\n' % hs_step,
            logfile, True)
        sea_states_2run = []
        while hs >= hs_min:
            log('------------------------- Running  Hs %.2f m -------------------------\n' % hs,
                logfile, True)
            log('Tps:', logfile, True)
            for tp in Tps: log(' %.2f' % tp, logfile, False)
            log('\n', logfile, False)
            # %%
            log('Pre-processing. Creating yml files.\n', logfile, True)
            sea_states_2run.append([hs, Tps])
            # update sea states to be post processed
            if round(hs, 3) not in sea_states_2post.keys():
                sea_states_2post[round(hs, 3)] = set(Tps)
            else:
                sea_states_2post[round(hs, 3)] = sea_states_2post[round(hs, 3)].union(set(Tps))

            preProcessing.main(hs, Tps, wave_dirs, model_file_name, fname_pattern, seeds,
                               seed_random_generator, jonswap_gamma)
            # %%
            log('Searching cases to be run.\n', logfile, True)
            os.chdir('runs')  # folder 'runs' is created in preProcessing
            i, c2g0, = 1, 0
            c2g_time_to_call_DOF = 30*60  # See (*) below
            while checkMissingResultsandResubmit.findMissingFiles(
                                                         fname_pattern, fname_missing,
                                                         sea_states_2run, wave_dirs, num_of_seeds,
                                                         progress_approach):
                c2g, st = estimate_time(fname_missing, frequency=simtime_estimate)

                # resubmiToDOF() must be called with more care since this piece of shit is
                # extremely slow and load cases thought ongoing will be finished before this call
                # is completed, causing them to be submitted again and re-run.
                #
                # That means that resubmiToDOF() must not be called too often, definitely not
                # every time findMissingFiles() is called.
                #
                # On the other hand, if called only once, some cases might still be missing after
                # DOF is conpleted, due to reasons like computers going offline, not able to obtain
                # a license, etc. For these resons, after DOF is finished with its first pass, if
                # there are cases still missing, it would be recommended to re-submit these cases
                # to DOF.
                #
                #  (*) CURRENT APPROACH
                #  Calling resubmiToDOF() if c2g (cases to go) doesn't change for 30 minutes.
                #  This time is set by the variable c2g_time_to_call_DOF.
                #
                if i == 1:
                    log('Submitting jobs. Check progress in DOF.\n', '..\\'+logfile, True)
                    checkMissingResultsandResubmit.resubmitToDOF(fname_missing)

                if not c2g == c2g0:
                    c2g_time = time.time()
                else:
                    time_from_last_change = time.time() - c2g_time
                    if time_from_last_change > c2g_time_to_call_DOF:  # See (*) above
                        c2g_time = time.time()
                        log('Too long since last progress. Re-submitting cases to DOF.\n',
                            '..\\'+logfile, True)
                        checkMissingResultsandResubmit.resubmitToDOF(fname_missing)

                log('Cases to go: %d. Checking again in %s.\n' % (c2g, strtimes(st)),
                    '..\\'+logfile, True)
                time.sleep(st)
                c2g0 = c2g
                i += 1
            os.chdir('..')
            # %%
            log('Concatenating batch results\n', logfile, True)
            CombineResults.combine(sea_states_2post, wave_dirs, num_of_seeds,
                                   concat_results_file, fname_pattern)

            # %%
            log('Gumbel fit\n', logfile, True)
            # GumbelFit returns 2 pandas panels: full and summary results.
            # Full results are used in plotting. Summary is used in postProcessing_py
            gumbel_res, gumbel_sum_res = GumbelFit.main(
                                              concat_results_file, confidence_level, num_of_seeds,
                                              summary_file_statistical, summary_file_loads,
                                              False, None, None, None, None)

            # %%
            log('Checking if results are acceptable\n', logfile, True)
            rerun_Tps = postProcessing.check_red_seastates(hs, gumbel_sum_res, vars_limits,
                                                           useMLE, logfile)
            if not rerun_Tps:
                log('All Tps acceptable.\n', logfile, True)
            else:
                log('Not acceptable Tps:', logfile, True)
                for tp in rerun_Tps: log(' %.2f' % tp, logfile, False)
                log('\n', logfile, False)
            allowable_weather_window[round(hs, 3)] = list(set(Tps) - set(rerun_Tps))
            w_window.update(hs, Tps, rerun_Tps)
            w_window.print_full_table(logfile, True)
            while True:
                # reduce Hs and get the list of Tps to be run:
                hs -= hs_step
                if hs < hs_min:
                    break
                Tps = w_window.get_tps2run(hs)
                if Tps:
                    break
                elif w_window.is_run_complete():  # no more sea states left to be run
                        hs = False
                        break

        # summary table in the end of each hs_step
        log('---------------------- Summary for Hs step of %.2fm ------------------\n' % hs_step,
            logfile, True)
        w_window.print_simple_table(logfile, True)

    # ### #########################################################################################
    # DONE WITH LOOPS - SHOW FINAL RESULTS
    # ### #########################################################################################

    log('=========================== Final Results ============================\n', logfile, True)

    # Prints to screen and to file a summary of static and dynamic loads, returns static loads
    static_loads = summary_loads(gumbel_sum_res, vars_limits, useMLE, w_window,
                                 logfile, summary_file_wwindow)

    # Shows results table in text model
    w_window.print_simple_table(summary_file_wwindow, toscreen=False)
    w_window.print_window(summary_file_wwindow, logfile)

    # Saves spreadsheet with weather window
    log('Creating spreadsheet with results.\n', logfile, True)
    summary_file_wwindow_xl = os.path.splitext(summary_file_wwindow)[0] + '.xlsx'
    create_results_xl.main(info_header, w_window.hs_table, summary_file_wwindow_xl,
                           tp_start, vars_limits, gumbel_sum_res, static_loads, useMLE)

    # Create Gumbel plots for limiting sea states
    if plot:
        create_gumbel_plots(gumbel_res, gumbel_sum_res, vars_limits, useMLE, w_window,
                            num_of_seeds, confidence_level, concat_results_file, logfile)

    log('For detailed results tables with loads, see "%s".\n' % summary_file_loads, logfile, True)
    log('For summary results, see: "%s".\n' % summary_file_wwindow, logfile, True)
    log('For summary results, see: "%s".\n' % summary_file_wwindow_xl, logfile, True)
