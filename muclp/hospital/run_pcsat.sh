#!/usr/bin/env bash
# Run PCSat (CoAR) on a pfwCSP .smt2 file.
# usage: run_pcsat.sh COAR_DIR CONFIG.json FILE.smt2 TIMEOUT_SECONDS
# Prints "VERDICT MILLISECONDS" on the first line, then the solution (define-fun lines) if any.
# (called by compare_hospital.py, directly on Linux or through wsl.exe on Windows)
cd "$1" || { echo "error 0"; exit 0; }
start=$(date +%s%N)
out=$(timeout "$4" ./_build/default/main.exe -c "$2" -p pfwcsp "$3" 2>/dev/null)
code=$?
ms=$(( ($(date +%s%N) - start) / 1000000 ))
if   echo "$out" | grep -q '^(define-fun'; then verdict=sat
elif echo "$out" | grep -q '^unsat';       then verdict=unsat
elif echo "$out" | grep -q '^sat';         then verdict=sat
elif echo "$out" | grep -q '^unknown';     then verdict=unknown
elif [ "$code" -eq 124 ];                  then verdict=timeout
else verdict=error
fi
echo "$verdict $ms"
echo "$out" | grep '^(define-fun'
