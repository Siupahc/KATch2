#!/usr/bin/env bash
# Run nksynth inside WSL / Linux: run_nksynth.sh BINARY ARGS...  (BINARY may start with ~)
# (called by compare_hospital.py through wsl.exe on Windows)
b="${1/#\~/$HOME}"; shift
exec "$b" "$@"
