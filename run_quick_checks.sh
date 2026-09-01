#!/bin/sh
# Quick end-to-end checks (~2 min). Lean check documented in README.
set -e
PY=${PYTHON:-python3}
echo "== P1: foundation self-checks =="
( cd p1 && $PY collatz.py )
echo "== P1: independent certificate verification =="
( cd p1 && $PY verify.py )
echo "== P1: adaptive-barrier checks (Theorem A') =="
( cd p1 && $PY exp27_adaptive_barrier.py )
echo "== P1: counterexample-count checks (Corollary) =="
( cd p1 && $PY exp28_exceptional_count.py )
echo "== P2: 2-adic cycle-law verification (Theorem 6.2) =="
( cd p2 && $PY exp29_cstat_verify.py )
echo "ALL QUICK CHECKS PASSED"
