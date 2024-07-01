#!/usr/bin/env python3

from tabulate import tabulate
import subprocess

TOOL = ["dune", "exec", "gtypes"]
LOG = "table-type-inference.log"

BENCHS = [
    ("branching", "branching/branching-covered"),
    ("coordination", "coordination/coordination-covered"),
    ("drill", "drill/drill-covered"),
    ("ex-1", "ex-1/ex-1-covered"),
    ("gaussian", "gaussian/gaussian-covered"),
    ("gbm", "gbm/gbm-covered"),
    ("gda", "gda/gda-covered"),
    ("gmm", "gmm/gmm-covered"),
    ("grw", "grw/grw-covered"),
    ("hmm", "hmm/hmm-covered"),
    ("kalman", "kalman/kalman-covered"),
    ("kalman-chaos", "kalman-chaos/kalman-chaos-covered"),
    ("lr", "lr/lr-covered"),
    ("run-factory", "run-factory/run-factory-covered"),
    ("scientists","scientists/scientists-covered"),
    ("seq", "recursive/seq/seq-covered"),
    ("sprinkler", "sprinkler/sprinkler-covered"),
    ("user-behavior", "user-behavior/user-behavior-covered"),
    ("vae", "vae/vae-covered"),
    ("weight", "weight/weight-covered"),
    ("aircraft", "aircraft/aircraft-covered"),
    ("iter", "recursive/iter/iter-covered"),
    ("marsaglia", "marsaglia/marsaglia-covered"),
    ("ptrace", "ptrace/ptrace-covered"),
    ("ex-2-covered-aligned", "ex-2/ex-2-covered-aligned"),
    ("ex-2-covered-misaligned", "ex-2/ex-2-covered-misaligned"),
    ("diter-covered-aligned", "recursive/diter/diter-covered-aligned"),
    ("diter-covered-misaligned", "recursive/diter/diter-covered-misaligned"),
    ("gp-dsl-covered-aligned", "gp-dsl/gp-dsl-covered-aligned"),
    ("gp-dsl-covered-misaligned", "gp-dsl/gp-dsl-covered-misaligned"),
    ("recur-covered-aligned", "recursive/recur/recur-covered-aligned"),
    ("recur-covered-misaligned", "recursive/recur/recur-covered-misaligned")
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
