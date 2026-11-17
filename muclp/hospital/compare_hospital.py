#!/usr/bin/env python3
"""Hospital example: KATch2-synth (`nksynth`) vs PCSat (CoAR, pfwCSP) on the same synthesis problem.

Problem: hospital_test.pdf. Find the policy X of the core switch S such that
  N1  traffic for W, and non-FTP traffic for M, is delivered;
  N2  FTP traffic never reaches M;
  N3  S only forwards (+ step 7, anti-spoofing: S may only rewrite the port).

Files (same directory):
  hospital_nospoof.nksynth   KATch2, N3 + anti-spoofing   <- same spec as the three .smt2
  hospital.nksynth           KATch2, N3 as in the pdf (T: S may also rewrite dst/typ)
  hospital_wf.smt2           pfwCSP, pdf section 4, W free well-founded unknown
  hospital_bfs.smt2          pfwCSP, W fixed by BFS distances (pdf section 5)
  hospital_opt.smt2          pfwCSP, W fixed + hole reduced to "choose the port" + known
                             steps written without existential (only 1 skolem function)

PCSat is randomised (very different times from one run to the next): each (file, config)
is run --reps times. KATch2 is deterministic: run once.

Examples:
    python compare_hospital.py                                   # everything, 300 s timeout
    python compare_hospital.py --timeout 120 --reps 5 --configs pcsat_tbq_sol
    python compare_hospital.py --only katch2
    python compare_hospital.py --smt2 hospital_opt.smt2 --nksynth hospital_nospoof.nksynth

On Windows, PCSat is called inside WSL (`wsl.exe`); on Linux, directly.
"""

import argparse
import csv
import os
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ON_WINDOWS = platform.system() == "Windows"

NKSYNTH = ["hospital_nospoof.nksynth", "hospital.nksynth"]
SMT2 = ["hospital_opt.smt2", "hospital_bfs.smt2", "hospital_wf.smt2"]
CONFIGS = ["pcsat_tbq_sol", "pcsat_ppm_tbq_ar_sol"]  # in configs/ (same as CoAR's, + solution printing)


def to_wsl_path(p: Path) -> str:
    s = str(p.resolve())
    if len(s) > 1 and s[1] == ":":
        return f"/mnt/{s[0].lower()}{s[2:].replace(os.sep, '/')}"
    return s.replace(os.sep, "/")


# ───────────────────────────── KATch2 ─────────────────────────────

def katch2_cmd(binary, distro, *args):
    """`binary` prefixed with `wsl:` runs inside WSL (paths are translated)."""
    if binary.startswith("wsl:"):
        conv = [to_wsl_path(a) if isinstance(a, Path) else a for a in args]
        return ["wsl.exe", "-d", distro, "--", "bash", "-l", to_wsl_path(HERE / "run_nksynth.sh"), binary[4:], *conv]
    return [binary, *[str(a) for a in args]]


def run_katch2(binary, nk_file, timeout, extra, distro):
    """-> (verdict, ms, solution text).  Time includes process start-up (and wsl.exe, if used)."""
    with tempfile.TemporaryDirectory() as tmp:
        sol = Path(tmp) / "sol.nksol"
        start = time.perf_counter()
        try:
            r = subprocess.run(katch2_cmd(binary, distro, nk_file, "--output", sol, *extra),
                               capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "timeout", timeout * 1000, ""
        ms = int((time.perf_counter() - start) * 1000)
        first = (r.stdout.strip().splitlines() or [""])[0]
        verdict = {"SAT": "sat", "UNSAT": "unsat", "UNKNOWN": "unknown"}.get(first, "error")
        if verdict == "error":
            print(f"  [katch2] {nk_file.name}: {(r.stderr or r.stdout).strip()[:300]}", file=sys.stderr)
        text = sol.read_text(encoding="utf-8").strip() if sol.exists() else ""
        if verdict == "sat":  # independent re-check of the synthesized hole
            chk = subprocess.run(katch2_cmd(binary, distro, nk_file, "--check", sol),
                                 capture_output=True, text=True, timeout=max(timeout, 60))
            text = f"[--check: {chk.stdout.strip()}] [{len(text)} chars] {text}"
        return verdict, ms, text


# ───────────────────────────── PCSat ─────────────────────────────

def run_pcsat(coar_dir, config, smt2_file, timeout, distro):
    """-> (verdict, ms, solution of X)"""
    script, cfg = HERE / "run_pcsat.sh", HERE / "configs" / f"{config}.json"
    if ON_WINDOWS:
        cmd = ["wsl.exe", "-d", distro, "--", "bash", "-l", to_wsl_path(script),
               coar_dir, to_wsl_path(cfg), to_wsl_path(smt2_file), str(timeout)]
    else:
        cmd = ["bash", str(script), os.path.expanduser(coar_dir), str(cfg), str(smt2_file), str(timeout)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 60)
    except subprocess.TimeoutExpired:
        return "timeout", timeout * 1000, ""
    lines = r.stdout.replace("\0", "").strip().splitlines()
    if not lines or len(lines[0].split()) < 2:
        return "error", 0, r.stderr.strip()[:300]
    verdict, ms = lines[0].split()[:2]
    x_def = next((l for l in lines[1:] if l.startswith("(define-fun |X|")), "")
    return verdict, int(ms), x_def


# ───────────────────────────── reporting ─────────────────────────────

def summary(results, timeout):
    """results: list of (verdict, ms). -> 'k/n sat, median, min-max' string."""
    n = len(results)
    solved = [ms for v, ms in results if v in ("sat", "unsat")]
    verdicts = {v for v, _ in results if v in ("sat", "unsat")}
    if not solved:
        return f"0/{n} solved (timeout {timeout}s)" if n > 1 else f"{results[0][0]} {results[0][1] / 1000:.1f}s"
    v = "/".join(sorted(verdicts))
    if n == 1:
        return f"{v} {solved[0] / 1000:.2f}s"
    return (f"{len(solved)}/{n} {v}, median {statistics.median(solved) / 1000:.1f}s, "
            f"min {min(solved) / 1000:.1f}s, max {max(solved) / 1000:.1f}s")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", choices=["katch2", "pcsat"], help="run only one of the two tools")
    ap.add_argument("--nksynth", nargs="+", default=NKSYNTH, help=f"KATch2 files (default: {' '.join(NKSYNTH)})")
    ap.add_argument("--smt2", nargs="+", default=SMT2, help=f"PCSat files (default: {' '.join(SMT2)})")
    ap.add_argument("--configs", nargs="+", default=CONFIGS, help="PCSat configs from configs/")
    ap.add_argument("--reps", type=int, default=3, help="PCSat runs per (file, config) (default 3)")
    ap.add_argument("--jobs", type=int, default=6, help="PCSat runs in parallel (default 6)")
    ap.add_argument("--timeout", type=int, default=300, help="seconds per solver call (default 300)")
    ap.add_argument("--katch2-flags", nargs="*", default=[], help="extra nksynth flags, e.g. --no-clause-merge")
    # Since the merge of mb64/synth (CaDiCaL), nksynth no longer builds with MSVC: on Windows it is
    # built and run in WSL (CARGO_TARGET_DIR=~/katch2-target cargo build --release).
    ap.add_argument("--katch2", default="wsl:~/katch2-target/release/nksynth" if ON_WINDOWS
                    else str(REPO / "target" / "release" / "nksynth"),
                    help="nksynth binary; prefix `wsl:` to run it inside WSL")
    ap.add_argument("--coar", default="~/coar", help="CoAR directory (inside WSL on Windows)")
    ap.add_argument("--distro", default="Ubuntu", help="WSL distribution (Windows only)")
    ap.add_argument("--csv", default=str(HERE / "results.csv"))
    args = ap.parse_args()

    rows = []  # (tool, file, config, rep, verdict, ms, solution)
    katch2 = args.katch2

    # PCSat runs go first, in the background (they are the slow part); KATch2 runs meanwhile.
    pool = ThreadPoolExecutor(max_workers=args.jobs)
    jobs = []
    if args.only != "katch2":
        for f in args.smt2:
            for c in args.configs:
                for i in range(1, args.reps + 1):
                    fut = pool.submit(run_pcsat, args.coar, c, HERE / f, args.timeout, args.distro)
                    jobs.append(((f, c, i), fut))

    if args.only != "pcsat":
        if not katch2.startswith("wsl:") and not Path(katch2).exists():
            sys.exit(f"KATch2 binary not found: {katch2} (run cargo build --release)")
        for f in args.nksynth:
            v, ms, sol = run_katch2(katch2, HERE / f, args.timeout, args.katch2_flags, args.distro)
            cfg = " ".join(args.katch2_flags) or "default"
            rows.append(("katch2", f, cfg, 1, v, ms, sol))
            print(f"katch2  {f:28} {cfg:22} {v:8} {ms / 1000:8.2f}s  {sol[:120]}", flush=True)

    for (f, c, i), fut in jobs:
        v, ms, sol = fut.result()
        rows.append(("pcsat", f, c, i, v, ms, sol))
        print(f"pcsat   {f:28} {c:22} #{i} {v:8} {ms / 1000:8.2f}s", flush=True)
    pool.shutdown()

    # summary table: one line per (tool, file, config)
    print("\n" + "=" * 100)
    groups = {}
    for tool, f, c, _, v, ms, sol in rows:
        groups.setdefault((tool, f, c), []).append((v, ms, sol))
    for (tool, f, c), res in groups.items():
        print(f"{tool:7} {f:28} {c:22} {summary([(v, ms) for v, ms, _ in res], args.timeout)}")
    print("=" * 100)
    # one synthesized X per PCSat file (they are all equivalent up to useless guards)
    shown = set()
    for tool, f, c, _, v, ms, sol in rows:
        if tool == "pcsat" and v == "sat" and sol and f not in shown:
            shown.add(f)
            print(f"\nX synthesized by PCSat on {f} ({c}):\n  {re.sub(r'[|]', '', sol)}")

    with open(args.csv, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["tool", "file", "config", "rep", "verdict", "ms", "solution"])
        w.writerows(rows)
    print(f"\nResults: {args.csv}")


if __name__ == "__main__":
    main()
