#!/usr/bin/env bash
# Run a CoAR solver on a .hes file and print "VERDICT MILLISECONDS".
# usage: run_coar.sh COAR_DIR CONFIG FILE.hes TIMEOUT_SECONDS
# (called by compare.py, directly on Linux or through wsl.exe on Windows)
cd "$1" || { echo "error 0"; exit 0; }
start=$(date +%s%N)
out=$(timeout "$4" ./_build/default/main.exe -c "./config/solver/$2.json" -p muclp "$3" 2>/dev/null | tail -1)
ms=$(( ($(date +%s%N) - start) / 1000000 ))
if [ -z "$out" ]; then
  if [ "$ms" -ge $(( $4 * 1000 )) ]; then out=timeout; else out=error; fi
fi
echo "${out%%,*} $ms"
