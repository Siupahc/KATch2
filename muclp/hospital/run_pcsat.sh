#!/usr/bin/env bash
# Run PCSat (CoAR) on a pfwCSP .smt2 file.
# usage: run_pcsat.sh COAR_DIR CONFIG.json FILE.smt2 TIMEOUT_SECONDS
# Prints "VERDICT MILLISECONDS" on the first line, then the solution (define-fun lines) if any.
# (called by compare_hospital.py, directly on Linux or through wsl.exe on Windows)
cd "$1" || { echo "error 0"; exit 0; }
ms_start=$(python3 -c 'import time; print(int(time.monotonic()*1000))')
out=$(timeout "$4" ./_build/default/main.exe -c "$2" -p pfwcsp "$3" 2>/dev/null)
code=$?
ms_end=$(python3 -c 'import time; print(int(time.monotonic()*1000))')
ms=$(( ms_end - ms_start ))
if   echo "$out" | grep -q '^(define-fun'; then verdict=sat
elif echo "$out" | grep -Eq '^(unsat|\(fail\)|infeasible)'; then verdict=unsat
elif echo "$out" | grep -q '^sat';         then verdict=sat
elif echo "$out" | grep -q '^unknown';     then verdict=unknown
elif [ "$code" -eq 124 ];                  then verdict=timeout
else verdict=error
fi
echo "$verdict $ms"
echo "$out" | grep '^(define-fun'
