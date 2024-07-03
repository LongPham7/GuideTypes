#!/usr/bin/env python3

from tabulate import tabulate
import subprocess

TOOL = ["dune", "exec", "gtypes"]
LOG = "table-coverage-checking.log"

BENCHS = [
    ("branching", "branching/branching-covered", "branching/branching-uncovered"),
    ("coordination", "coordination/coordination-covered",
     "coordination/coordination-uncovered"),
    ("drill", "drill/drill-covered", "drill/drill-uncovered"),
    ("ex-1", "ex-1/ex-1-covered", "ex-1/ex-1-uncovered"),
    ("gaussian", "gaussian/gaussian-covered", "gaussian/gaussian-uncovered"),
    ("gbm", "gbm/gbm-covered", "gbm/gbm-uncovered"),
    ("gda", "gda/gda-covered", "gda/gda-uncovered"),
    ("gmm", "gmm/gmm-covered", "gmm/gmm-uncovered"),
    ("grw", "grw/grw-covered", "grw/grw-uncovered"),
    ("hmm", "hmm/hmm-covered", "hmm/hmm-uncovered"),
    ("kalman", "kalman/kalman-covered", "kalman/kalman-uncovered"),
    ("kalman-chaos", "kalman-chaos/kalman-chaos-covered",
     "kalman-chaos/kalman-chaos-uncovered"),
    ("lr", "lr/lr-covered", "lr/lr-uncovered"),
    ("run-factory", "run-factory/run-factory-covered",
     "run-factory/run-factory-uncovered"),
    ("scientists", "scientists/scientists-covered",
     "scientists/scientists-uncovered"),
    ("seq", "seq/seq-covered", "seq/seq-uncovered"),
    ("sprinkler", "sprinkler/sprinkler-covered", "sprinkler/sprinkler-uncovered"),
    ("user-behavior", "user-behavior/user-behavior-covered",
     "user-behavior/user-behavior-uncovered"),
    ("vae", "vae/vae-covered", "vae/vae-uncovered"),
    ("weight", "weight/weight-covered", "weight/weight-uncovered"),
    ("aircraft", "aircraft/aircraft-covered", "aircraft/aircraft-uncovered"),
    ("iter", "iter/iter-covered", "iter/iter-uncovered"),
    ("marsaglia", "marsaglia/marsaglia-covered", "marsaglia/marsaglia-uncovered"),
    ("ptrace", "ptrace/ptrace-covered", "ptrace/ptrace-uncovered"),
    ("ex-2-aligned", "ex-2/ex-2-covered-aligned",
     "ex-2/ex-2-uncovered-aligned"),
    ("ex-2-misaligned", "ex-2/ex-2-covered-misaligned",
     "ex-2/ex-2-uncovered-misaligned"),
    ("diter-aligned", "diter/diter-covered-aligned",
     "diter/diter-uncovered-aligned"),
    ("diter-misaligned", "diter/diter-covered-misaligned",
     "diter/diter-uncovered-misaligned"),
    ("gp-dsl-aligned", "gp-dsl/gp-dsl-covered-aligned",
     "gp-dsl/gp-dsl-uncovered-aligned"),
    ("gp-dsl-misaligned", "gp-dsl/gp-dsl-covered-misaligned",
     "gp-dsl/gp-dsl-uncovered-misaligned"),
    ("recur-aligned", "recur/recur-covered-aligned",
     "recur/recur-uncovered-aligned"),
    ("recur-misaligned", "recur/recur-covered-misaligned",
     "recur/recur-uncovered-misaligned")
]


def look_for_runtime(msg):
    lines = msg.splitlines()
    for line in lines:
        if line.find("total time") != -1:
            return line.split(":")[-1].strip()
    return "N/A"


def execute(out, task):
    name, path_covered, path_uncovered = task
    loc = "N/A"
    with open(path_covered, "r") as f:
        loc = str(len(f.readlines()))

    # Covered version
    cmd = TOOL + ["coverage-check", path_covered]
    ret = subprocess.run(cmd, stdout=subprocess.PIPE)
    msg_covered = str(ret.stdout, "utf-8")

    out.write("Benchmark {} covered\n".format(name))
    out.write("-" * 80 + "\n")
    out.write(msg_covered)
    out.write("=" * 80 + "\n\n\n")

    # Uncovered version
    cmd = TOOL + ["coverage-check", path_uncovered]
    ret = subprocess.run(cmd, stdout=subprocess.PIPE)
    msg_uncovered = str(ret.stdout, "utf-8")

    out.write("Benchmark {} uncovered\n".format(name))
    out.write("-" * 80 + "\n")
    out.write(msg_uncovered)
    out.write("=" * 80 + "\n\n\n")

    # Extract the analysis time
    time_covered = look_for_runtime(msg_covered)
    unit_covered = time_covered[-2:]
    time_uncovered = look_for_runtime(msg_uncovered)
    unit_uncovered = time_uncovered[-2:]
    if unit_covered != unit_uncovered:
        if unit_covered == "us" and unit_uncovered == "ms":
            time_covered = str(float(time_covered[:-2]) / 1000)
            unit_covered = "ms"
        elif unit_covered == "ms" and unit_uncovered == "us":
            time_uncovered = str(float(time_uncovered[:-2]) / 1000)
            unit_uncovered = "ms"
        else:
            raise Exception("Analysis time for the covered and uncovered cases have different units: {} and {}".format(
                unit_covered, unit_uncovered))

    total_time = float(time_covered[:-2]) + float(time_uncovered[:-2])
    precision = 3
    total_time_rounded_string = "{:.{precision}f}".format(
        total_time, precision=precision)

    return (name, path_covered, loc, total_time_rounded_string + unit_covered)


if __name__ == "__main__":
    with open(LOG, "w") as f:
        tab = []
        for bench in BENCHS:
            tab.append(execute(f, bench))
        print(tabulate(tab, headers=["Name", "Path", "LOC", "Check Time"]))
