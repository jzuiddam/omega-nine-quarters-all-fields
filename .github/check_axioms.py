#!/usr/bin/env python3
# Fails unless every `#print axioms` in Checks/Axioms.lean reports only the standard axioms.
"""Usage: check_axioms.py LEAN_OUTPUT_LOG CHECKS_FILE

Exit 0 only if the log contains exactly one axiom report for each `#print axioms NAME` command in
CHECKS_FILE, each report lists a subset of {propext, Classical.choice, Quot.sound}, and the log
mentions neither `sorryAx` nor an error.
"""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main(log_path, checks_path):
    log = open(log_path, encoding="utf-8").read()
    checks = open(checks_path, encoding="utf-8").read()
    expected = re.findall(r"^#print axioms\s+(\S+)\s*$", checks, re.M)
    problems = []
    if not expected:
        problems.append(f"no `#print axioms` commands found in {checks_path}")
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        reports.setdefault(name, []).append({a.strip() for a in axioms.split(",") if a.strip()})
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        reports.setdefault(name, []).append(set())
    for name in expected:
        got = reports.get(name, [])
        if len(got) != 1:
            problems.append(f"{name}: expected one axiom report, found {len(got)}")
        for axioms in got:
            extra = axioms - ALLOWED
            if extra:
                problems.append(f"{name}: non-standard axioms {sorted(extra)}")
    for name in reports:
        if name not in expected:
            problems.append(f"{name}: unexpected axiom report")
    if "sorryAx" in log:
        problems.append("log mentions sorryAx")
    if re.search(r"\berror\b", log):
        problems.append("log contains an error")
    for p in problems:
        print(f"FAILED: {p}")
    if problems:
        return 1
    print(f"OK: {len(expected)} axiom reports, all within {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
