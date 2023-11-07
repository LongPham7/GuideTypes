#!/usr/bin/env python3

from tabulate import tabulate
import subprocess

TOOL = ["dune", "exec", "gtypes"]
LOG = "table-type-checking.log"

BENCHS = [
    ("aircraft", "aircraft"),
    ("branching", "branching"),
    ("drill-or-not-with-sounding", "drill-or-not-with-sounding"),
    ("example-1", "example-1"),
    ("example-2", "example-2"),
    ("gaussian", "gaussian"),
    ("gda-trainer", "gda-trainer"),
    ("gmm-proposal", "gmm-proposal"),
    ("hmm", "hmm"),
    ("infer-drift", "infer-drift"),
    ("kalman", "kalman"),
    ("kalman-chaos-opt", "kalman-chaos-opt"),
    ("learn-gbm", "learn-gbm"),
    ("linear-regression", "linear-regression"),
    ("marsaglia-normal", "marsaglia-normal"),
    ("meet-by-chance", "meet-by-chance"),
    ("poisson-trace", "poisson-trace"),
    ("run-pencil-factory", "run-pencil-factory"),
    ("sprinkler-bayes-net", "sprinkler-bayes-net"),
    ("time-series", "time-series"),
    ("user-behavior-generative", "user-behavior-generative"),
    ("vae", "vae"),
    ("weight", "weight")
]


def look_for_runtime(msg):
    lines = msg.splitlines()
    for line in lines:
        if line.find("total time") != -1:
            return line.split(":")[-1].strip()
    return "N/A"


def execute(out, task):
    name, path = task
    loc = "N/A"
    with open(path, "r") as f:
        loc = str(len(f.readlines()))
    cmd = TOOL + ["type-check", path]
    ret = subprocess.run(cmd, stdout=subprocess.PIPE)
    msg = str(ret.stdout, "utf-8")

    out.write("Benchmark %s\n" % name)
    out.write("-" * 80 + "\n")
    out.write(msg)
    out.write("=" * 80 + "\n\n\n")

    return (name, path, loc, look_for_runtime(msg))


if __name__ == "__main__":
    with open(LOG, "w") as f:
        tab = []
        for bench in BENCHS:
            tab.append(execute(f, bench))
        print(tabulate(tab, headers=["Name", "Path", "LOC", "Check Time"]))
