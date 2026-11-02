#!/usr/bin/env bash
# Run MuStrat (3 times) and MuVal (once) on every .hes file of this folder.
# usage (Linux / WSL):  bash run.sh [COAR_DIR] [TIMEOUT_SECONDS]
# Every query here is VALID, so any "invalid" is a wrong answer.
COAR=${1:-$HOME/coar}
TO=${2:-30}
HERE=$(cd "$(dirname "$0")" && pwd)
RUN="$HERE/../../run_coar.sh"
printf "%-22s %-30s %s\n" "file" "mustrat (x3)" "muval"
for f in "$HERE"/*.hes; do
  s=""
  for _ in 1 2 3; do s="$s $(bash "$RUN" "$COAR" mustrat "$f" "$TO" | cut -d' ' -f1)"; done
  m=$(bash "$RUN" "$COAR" muval_parallel_exc_tbq_ar "$f" "$TO" | cut -d' ' -f1)
  printf "%-22s %-30s %s\n" "$(basename "$f")" "$s" "$m"
done
