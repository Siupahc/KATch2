#!/usr/bin/env python3
"""Compare KATch2 with the muCLP solvers of CoAR (MuVal, MuStrat, ...) on `.nkt` files.

For every check (member / equiv / incl) of every file:
  1. generate the `.nksynth` (KATch2) and one `.hes` per encoding in out/;
  2. run KATch2 (`nksynth`): SAT = true, UNSAT = false;
  3. run every CoAR solver on every encoding: valid = true, invalid = false;
  4. print a table and write out/results.csv.

KATch2 is the oracle: a ✗ marks a disagreement (translation bug or solver bug).

Examples:
    python compare.py                                  # all examples/*.nkt
    python compare.py examples/02_line.nkt --timeout 10
    python compare.py --solvers muval mustrat --encodings direct naive

On Windows, CoAR is called inside WSL (`wsl.exe`); on Linux, directly.
"""

import argparse
import csv
import glob
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

from nkt import NktError, check_to_hes, check_to_nksynth, parse_nkt

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
ON_WINDOWS = platform.system() == "Windows"

SOLVERS = {  # short name -> CoAR configuration (config/solver/<name>.json)
    "muval": "muval_parallel_exc_tbq_ar",
    "mustrat": "mustrat",
    "mucyc": "mucyc",
}


def to_wsl_path(p: Path) -> str:
    s = str(p.resolve())
    if len(s) > 1 and s[1] == ":":
        return f"/mnt/{s[0].lower()}{s[2:].replace(os.sep, '/')}"
    return s.replace(os.sep, "/")


def run_katch2(binary, nksynth_file, timeout):
    start = time.perf_counter()
    try:
        r = subprocess.run([str(binary), str(nksynth_file)], capture_output=True, text=True, timeout=timeout)
        ms = int((time.perf_counter() - start) * 1000)
        first = (r.stdout.strip().splitlines() or [""])[0]
        verdict = {"SAT": "true", "UNSAT": "false", "UNKNOWN": "unknown"}.get(first, "error")
        if verdict == "error":
            print(f"  [katch2] {nksynth_file.name}: {(r.stderr or r.stdout).strip()[:200]}", file=sys.stderr)
        return verdict, ms
    except subprocess.TimeoutExpired:
        return "timeout", timeout * 1000


def run_coar(coar_dir, config, hes_file, timeout, distro):
    script = HERE / "run_coar.sh"
    if ON_WINDOWS:
        cmd = ["wsl.exe", "-d", distro, "--", "bash", "-l", to_wsl_path(script),
               coar_dir, config, to_wsl_path(hes_file), str(timeout)]
    else:
        cmd = ["bash", str(script), os.path.expanduser(coar_dir), config, str(hes_file), str(timeout)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
        parts = r.stdout.replace("\0", "").split()
        if len(parts) < 2:
            return "error", 0
        verdict = {"valid": "true", "invalid": "false"}.get(parts[-2], parts[-2])
        return verdict, int(parts[-1])
    except subprocess.TimeoutExpired:
        return "timeout", timeout * 1000


def fmt(verdict, ms, ref=None):
    mark = ""
    if ref in ("true", "false") and verdict in ("true", "false"):
        mark = " ✓" if verdict == ref else " ✗"
    return f"{verdict} {ms / 1000:.2f}s{mark}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", help=".nkt files (default: examples/*.nkt)")
    ap.add_argument("--solvers", nargs="+", default=["muval", "mustrat"], choices=sorted(SOLVERS))
    ap.add_argument("--encodings", nargs="+", default=["direct", "naive"], choices=["direct", "naive"])
    ap.add_argument("--timeout", type=int, default=30, help="seconds per solver call (default 30)")
    ap.add_argument("--katch2", default=str(REPO / "target" / "release" / ("nksynth.exe" if ON_WINDOWS else "nksynth")))
    ap.add_argument("--coar", default="~/coar", help="CoAR directory (inside WSL on Windows)")
    ap.add_argument("--distro", default="Ubuntu", help="WSL distribution (Windows only)")
    ap.add_argument("--out", default=str(HERE / "out"), help="directory for generated files and the CSV")
    args = ap.parse_args()

    files = args.files or sorted(glob.glob(str(HERE / "examples" / "*.nkt")))
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    katch2 = Path(args.katch2)
    if not katch2.exists():
        sys.exit(f"KATch2 binary not found: {katch2} (run cargo build --release)")

    runs = [(s, e) for s in args.solvers for e in args.encodings]
    headers = ["file", "check", "kind", "katch2"] + [f"{s}/{e}" for s, e in runs]
    rows, disagreements = [], 0

    for f in files:
        src = Path(f)
        try:
            prob = parse_nkt(src.read_text(encoding="utf-8"))
        except NktError as err:
            print(f"{src.name}: parse error: {err}", file=sys.stderr)
            continue
        gen = out_dir / src.stem
        gen.mkdir(exist_ok=True)
        for chk in prob.checks:
            nk = gen / f"{chk.name}.nksynth"
            nk.write_text(check_to_nksynth(prob, chk), encoding="utf-8")
            ref, ref_ms = run_katch2(katch2, nk, args.timeout)
            row = [src.stem, chk.name, chk.kind, fmt(ref, ref_ms)]
            for solver, enc in runs:
                hes = gen / f"{chk.name}.{enc}.hes"
                hes.write_text(check_to_hes(prob, chk, enc), encoding="utf-8", newline="\n")
                v, ms = run_coar(args.coar, SOLVERS[solver], hes, args.timeout, args.distro)
                row.append(fmt(v, ms, ref))
                disagreements += v in ("true", "false") and ref in ("true", "false") and v != ref
            rows.append(row)
            print(" | ".join(row), flush=True)

    # final aligned table
    widths = [max(len(str(r[i])) for r in rows + [headers]) for i in range(len(headers))]
    line = lambda r: "  ".join(str(c).ljust(w) for c, w in zip(r, widths))
    print("\n" + line(headers) + "\n" + "  ".join("-" * w for w in widths))
    for r in rows:
        print(line(r))
    print(f"\n{len(rows)} checks, {disagreements} disagreement(s) with KATch2 (✗).")

    with open(out_dir / "results.csv", "w", newline="", encoding="utf-8") as fh:
        csv.writer(fh).writerows([headers] + rows)
    print(f"Results: {out_dir / 'results.csv'}  (generated files in {out_dir})")


if __name__ == "__main__":
    main()
