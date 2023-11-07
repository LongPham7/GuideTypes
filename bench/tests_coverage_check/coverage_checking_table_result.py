#!/usr/bin/env python3

from tabulate import tabulate
import subprocess

TOOL = ["dune", "exec", "gtypes"]
LOG = "table-coverage-checking.log"

BENCHS = [
    ("aircraft", "aircraft"),
    ("branching", "branching"),
    ("drill", "drill"),
    ("ex-1", "ex-1"),
    ("ex-2", "ex-2"),
    ("gaussian", "gaussian"),
    ("gda", "gda"),
    ("gmm", "gmm"),
    ("hmm", "hmm"),
    ("grw", "grw"),
    ("kalman", "kalman"),
    ("kalman-chaos", "kalman-chaos"),
    ("gbm", "gbm"),
    ("lr", "lr"),
    ("marsaglia", "marsaglia"),
    ("coordination", "coordination"),
    ("ptrace", "ptrace"),
    ("run-factory", "run-factory"),
    ("sprinkler", "sprinkler"),
    ("gp-dsl", "gp-dsl"),
    ("user-behavior", "user-behavior"),
    ("vae", "vae"),
    ("weight", "weight"),
    ("seq", "recursive/seq"),
    ("iter", "recursive/iter"),
    ("diter", "recursive/diter"),
    ("recur", "recursive/recur")
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
    cmd = TOOL + ["coverage-check", path]
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
