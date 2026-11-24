#!/usr/bin/env python3
"""Generate & benchmark Topology Zoo (and `.nksynth`) synthesis instances on KATch2 (`nksynth`)
vs CoAR (`PCSat`) across `nksynth_to_pcsat.py` optimization presets.

Supports:
  1. Direct `.nksynth` inputs (e.g. `hospital/hospital_nospoof.nksynth`, `experiments/Karen.nksynth`,
     `experiments/examples/Basnet-unsat.nksynth`).
  2. Direct `.gml` Topology Zoo inputs (e.g. `experiments/gml/Arpanet196912.gml`):
     uses `experiments/experiment.py` if `igraph` is installed, or an equivalent built-in pure-Python
     GML + BFS generator (zero external dependencies) with the exact same port assignment, shortest-path
     forwarding policy, and bad/good path selection!
     Also supports `--star-good` to emit Kleene-star reachability `spec <= in ; hop* ; out` (with
     optional `--filter-hole` `h1 <= 1`) so right-star path compilation (`compile_paths`) can be
     evaluated on Topology Zoo graphs too.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
import csv
import os
from pathlib import Path
import platform
import random
import re
import statistics
import subprocess
import sys
import tempfile
import time

from nksynth_to_pcsat import (
    PRESETS,
    compile_nksynth_to_pcsat,
    pcsat_model_to_nksol,
)

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
ON_WINDOWS = platform.system() == "Windows"


def to_wsl_path(p: Path) -> str:
    s = str(p.resolve())
    if len(s) > 1 and s[1] == ":":
        return f"/mnt/{s[0].lower()}{s[2:].replace(os.sep, '/')}"
    return s.replace(os.sep, "/")


# =============================================================================
# Built-in GML reader + Topology Zoo `.nksynth` generator (matches `experiments/experiment.py`)
# =============================================================================


def parse_gml_simple(gml_path: Path) -> tuple[list[str], list[tuple[int, int]]]:
    """Lightweight pure-Python Topology Zoo GML parser (fallback when `python-igraph` is absent)."""
    text = gml_path.read_text(encoding="utf-8", errors="ignore")
    toks = re.findall(r'"[^"]*"|\[|\]|[^\s\[\]"]+', text)
    pos = 0

    def parse_block() -> list[tuple[str, object]]:
        nonlocal pos
        items: list[tuple[str, object]] = []
        while pos < len(toks) and toks[pos] != "]":
            key = toks[pos]
            pos += 1
            if pos >= len(toks):
                break
            if toks[pos] == "[":
                pos += 1
                items.append((key, parse_block()))
                if pos < len(toks) and toks[pos] == "]":
                    pos += 1
            else:
                val = toks[pos]
                pos += 1
                if val.startswith('"') and val.endswith('"'):
                    val = val[1:-1]
                items.append((key, val))
        return items

    top = parse_block()
    graph_items: list[tuple[str, object]] = []
    for k, v in top:
        if k == "graph" and isinstance(v, list):
            graph_items = v
            break

    id_to_idx: dict[int, int] = {}
    labels: list[str] = []
    edges: list[tuple[int, int]] = []
    for k, v in graph_items:
        if k == "node" and isinstance(v, list):
            d = dict(v)
            nid = int(str(d["id"]))
            idx = len(labels)
            id_to_idx[nid] = idx
            labels.append(str(d.get("label", idx)))
        elif k == "edge" and isinstance(v, list):
            d = dict(v)
            s = id_to_idx[int(str(d["source"]))]
            t = id_to_idx[int(str(d["target"]))]
            edges.append((s, t))
    return labels, edges


def nk_name(label: str) -> str:
    label = re.sub(r"\s+", "_", label)
    label = re.sub(r"[^A-Za-z0-9_]", "_", label)
    if label and label[0].isdigit():
        label = "_" + label
    return label


def generate_topozoo_nksynth(
    gml_path: Path,
    num_bad: int = 1,
    num_good: int = 3,
    seed: int = 3,
    force_unsat: bool = False,
    star_good: bool = False,
    filter_hole: bool = False,
) -> tuple[str, int, int]:
    """Generate a `.nksynth` problem from a Topology Zoo `.gml` file, returning `(source, n_nodes, n_edges)`."""
    labels_raw, edges = parse_gml_simple(gml_path)
    n_nodes = len(labels_raw)
    n_edges = len(edges)
    labels = [nk_name(lb) for lb in labels_raw]

    rng = random.Random(seed)
    port_of: dict[tuple[int, int], int] = {}
    next_port: dict[int, int] = defaultdict(lambda: 1)
    adj: dict[int, list[int]] = defaultdict(list)

    for u, v in edges:
        if (u, v) not in port_of:
            port_of[(u, v)] = next_port[u]
            next_port[u] += 1
            adj[u].append(v)
        if (v, u) not in port_of:
            port_of[(v, u)] = next_port[v]
            next_port[v] += 1
            adj[v].append(u)

    max_port = max(next_port.values(), default=2) - 1
    port_bits = max(1, max_port.bit_length())
    loc_bits = max(1, n_nodes.bit_length())

    b_loc = f"x[0..{loc_bits}]"
    b_dst = f"x[{loc_bits}..{2 * loc_bits}]"
    b_port = f"x[{2 * loc_bits}..{2 * loc_bits + port_bits}]"
    b_dir = f"x[{2 * loc_bits + port_bits}..{2 * loc_bits + port_bits + 1}]"

    # All-pairs BFS shortest paths (deterministic neighbor order matching vertex index order)
    next_hop: dict[tuple[int, int], int] = {}
    paths: list[list[int]] = []
    for src in range(n_nodes):
        parent: dict[int, int | None] = {src: None}
        q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in parent:
                    parent[v] = u
                    q.append(v)
        for dst in range(n_nodes):
            if src == dst or dst not in parent:
                continue
            path: list[int] = []
            cur: int | None = dst
            while cur is not None:
                path.append(cur)
                cur = parent[cur]
            path.reverse()
            if len(path) < 2:
                continue
            paths.append(path)
            for i in range(len(path) - 1):
                next_hop.setdefault((path[i], dst), path[i + 1])

    if force_unsat:
        cands = [p for p in paths if len(p) >= 3]
        if not cands:
            cands = paths
        good_paths = rng.sample(cands, min(num_good, len(cands)))
        bad_paths = []
        for _ in range(num_bad):
            p = rng.choice(good_paths)
            start = rng.randrange(0, max(1, len(p) - 1))
            bad_paths.append(p[start:])
    else:
        bad_paths = rng.sample(paths, min(num_bad, len(paths)))
        cands = [
            p
            for p in paths
            if p not in bad_paths
            and not any(b[-1] == p[-1] and b[0] in p for b in bad_paths)
        ]
        good_paths = rng.sample(cands, min(num_good, len(cands)))

    lines: list[str] = [
        f"// Topology Zoo: {gml_path.name} (nodes={n_nodes}, edges={n_edges}, bad={len(bad_paths)}, good={len(good_paths)})",
        f"// Fields: loc = {b_loc}  dst = {b_dst}  port = {b_port}  dir = {b_dir}",
        "",
        "def topo =",
    ]
    topo_terms: list[str] = []
    for u, v in edges:
        pu, pv = port_of[(u, v)], port_of[(v, u)]
        for s, sp, d, dp in [(u, pu, v, pv), (v, pv, u, pu)]:
            topo_terms.append(
                f"    ({b_loc}~{s + 1}; {b_port}~{sp}; {b_dir}~1; {b_loc}:={d + 1}; {b_port}:={dp}; {b_dir}:=0)"
            )
    lines.append(" +\n".join(topo_terms))
    lines.append("\ndef pol =")
    pol_terms: list[str] = []
    for (here, dst), nxt in sorted(
        next_hop.items(), key=lambda it: (labels[it[0][0]], labels[it[0][1]])
    ):
        op = port_of[(here, nxt)]
        pol_terms.append(
            f"    ({b_loc}~{here + 1}; {b_dst}~{dst + 1}; {b_dir}~0; {b_port}:={op}; {b_dir}:=1)"
        )
    lines.append(" +\n".join(pol_terms))
    lines.append("")
    lines.append("hole h1")
    lines.append("def hop = h1; pol; topo")
    lines.append("def net = hop*" if star_good else "def net = (hop; dup)*")
    if filter_hole:
        lines.append("assert h1 <= 1")
    lines.append("")

    for p in bad_paths:
        s, d = p[0] + 1, p[-1] + 1
        lines.append(f"// BAD: {' -> '.join(labels[v] for v in p)}")
        lines.append(f"assert {b_loc}~{s}; {b_dst}~{d}; net; {b_loc}~{d} = 0")
    lines.append("")

    for p in good_paths:
        lines.append(f"// GOOD: {' -> '.join(labels[v] for v in p)}")
        s = p[0] + 1
        d = p[-1] + 1
        last_port = port_of[(p[-1], p[-2])]
        if star_good:
            lines.append(
                f"assert ({b_loc}~{s}; {b_port}~0; {b_dir}~0; {b_dst}~{d}; {b_loc}:={d}; {b_port}:={last_port}) "
                f"<= ({b_loc}~{s}; {b_port}~0; {b_dir}~0; {b_dst}~{d}; net; {b_loc}~{d})"
            )
        else:
            first = f"{b_loc}~{s}; {b_port}~0; {b_dir}~0; {b_dst}~{d}; "
            items = [
                f"{b_loc}:={p[i] + 1}; {b_port}:={port_of[(p[i], p[i - 1])]}"
                for i in range(1, len(p))
            ]
            hops = "; dup; ".join(["hop"] * len(items))
            lines.append(f"assert ({first}{'; dup; '.join(items)}) <= {hops}")

    return "\n".join(lines) + "\n", n_nodes, n_edges


# =============================================================================
# Solvers: KATch2 (`nksynth`) and CoAR (`PCSat`)
# =============================================================================


def run_nksynth(
    binary: str, nk_file: Path, timeout: int, distro: str, check_sol: Path | None = None
) -> tuple[str, int]:
    extra = ["--check", check_sol] if check_sol is not None else []
    if binary.startswith("wsl:"):
        conv = [to_wsl_path(a) if isinstance(a, Path) else str(a) for a in [nk_file, *extra]]
        py_runner = (
            "import os, subprocess, sys, time; "
            "b = os.path.expanduser(sys.argv[1]); "
            "t0 = time.monotonic(); "
            f"r = subprocess.run([b, *sys.argv[2:]], capture_output=True, text=True, timeout={timeout}); "
            "ms = int((time.monotonic() - t0) * 1000); "
            "lines = [l.strip() for l in r.stdout.splitlines() if l.strip()]; "
            "print((lines[-1] if lines else 'ERROR'), ms)"
        )
        cmd = ["wsl.exe", "-d", distro, "--", "python3", "-c", py_runner, binary[4:], *conv]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 15)
        except subprocess.TimeoutExpired:
            return "timeout", timeout * 1000
        parts = r.stdout.strip().split()
        if len(parts) < 2:
            if "subprocess.TimeoutExpired" in r.stderr:
                return "timeout", timeout * 1000
            return "error", 0
        last, ms = parts[-2], int(parts[-1])
    else:
        cmd = [binary, str(nk_file), *(str(a) for a in extra)]
        start = time.perf_counter()
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 15)
        except subprocess.TimeoutExpired:
            return "timeout", timeout * 1000
        ms = int((time.perf_counter() - start) * 1000)
        lines = [ln.strip() for ln in r.stdout.splitlines() if ln.strip()]
        last = lines[-1] if lines else ""
    if check_sol is not None:
        return last.lower(), ms
    return {"SAT": "sat", "UNSAT": "unsat", "UNKNOWN": "unknown"}.get(last, "error"), ms


def run_pcsat(
    coar_dir: str, config: str, smt2_file: Path, timeout: int, distro: str
) -> tuple[str, int, str]:
    script = HERE / "hospital" / "run_pcsat.sh"
    cfg = HERE / "hospital" / "configs" / f"{config}.json"
    if ON_WINDOWS:
        cmd = [
            "wsl.exe",
            "-d",
            distro,
            "--",
            "bash",
            "-l",
            to_wsl_path(script),
            coar_dir,
            to_wsl_path(cfg),
            to_wsl_path(smt2_file),
            str(timeout),
        ]
    else:
        cmd = ["bash", str(script), os.path.expanduser(coar_dir), str(cfg), str(smt2_file), str(timeout)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
    except subprocess.TimeoutExpired:
        return "timeout", timeout * 1000, ""
    lines = r.stdout.replace("\0", "").strip().splitlines()
    if not lines or len(lines[0].split()) < 2:
        return "error", 0, r.stderr.strip()[:200]
    verdict, ms = lines[0].split()[:2]
    defs = "\n".join(ln for ln in lines[1:] if ln.startswith("(define-fun"))
    return verdict, int(ms), defs


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("inputs", nargs="+", type=Path, help="`.gml` or `.nksynth` files")
    ap.add_argument("--presets", nargs="+", default=["generic", "all"], choices=PRESETS)
    ap.add_argument("--configs", nargs="+", default=["pcsat_tbq_sol"])
    ap.add_argument("--reps", type=int, default=1, help="PCSat repetitions per (instance, preset, config)")
    ap.add_argument("--jobs", type=int, default=2, help="Parallel PCSat workers (default 2)")
    ap.add_argument("--timeout", type=int, default=60, help="Solver timeout in seconds (default 60)")
    ap.add_argument("--num-bad", type=int, default=1)
    ap.add_argument("--num-good", type=int, default=2)
    ap.add_argument("--seed", type=int, default=3)
    ap.add_argument("--force-unsat", action="store_true")
    ap.add_argument("--star-good", action="store_true", help="Use Kleene star `hop*` for Topology Zoo good paths")
    ap.add_argument("--filter-hole", action="store_true", help="Add `assert h1 <= 1` (ACL/filter hole) on GML inputs")
    ap.add_argument("--verify", action="store_true", help="Verify PCSat SAT models with `nksynth --check` when small")
    ap.add_argument(
        "--katch2",
        default="wsl:~/katch2-target/release/nksynth"
        if ON_WINDOWS
        else str(REPO / "target" / "release" / "nksynth"),
    )
    ap.add_argument("--coar", default="~/coar")
    ap.add_argument("--distro", default="Ubuntu")
    ap.add_argument("--out-dir", type=Path, default=HERE / "out" / "topozoo")
    ap.add_argument("--csv", type=Path, default=HERE / "out" / "topozoo" / "results.csv")
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.csv.parent.mkdir(parents=True, exist_ok=True)

    prepared: list[tuple[str, Path, dict[str, tuple[Path, object]]]] = []
    translation_ms: dict[tuple[str, str], int] = {}
    for inp in args.inputs:
        stem = inp.stem
        if inp.suffix.lower() == ".gml":
            tag = stem + ("_unsat" if args.force_unsat else "") + ("_star" if args.star_good else "")
            nk_src, nn, ne = generate_topozoo_nksynth(
                inp,
                num_bad=args.num_bad,
                num_good=args.num_good,
                seed=args.seed,
                force_unsat=args.force_unsat,
                star_good=args.star_good,
                filter_hole=args.filter_hole,
            )
            nk_path = args.out_dir / f"{tag}.nksynth"
            nk_path.write_text(nk_src, encoding="utf-8", newline="\n")
            label = f"{tag} (V={nn},E={ne})"
        else:
            tag = stem
            nk_src = inp.read_text(encoding="utf-8")
            nk_path = inp
            label = stem

        preset_files: dict[str, tuple[Path, object]] = {}
        for pr in args.presets:
            start = time.perf_counter()
            _, csp, smt2 = compile_nksynth_to_pcsat(nk_src, preset=pr)
            translation_ms[label, pr] = round(1000 * (time.perf_counter() - start))
            smt_path = args.out_dir / f"{tag}.{pr}.smt2"
            smt_path.write_text(smt2, encoding="utf-8", newline="\n")
            preset_files[pr] = (smt_path, csp)
        prepared.append((label, nk_path, preset_files))

    rows: list[list[object]] = []
    pool = ThreadPoolExecutor(max_workers=args.jobs)
    pcsat_futs = []

    for label, nk_path, preset_files in prepared:
        for pr, (smt_path, csp) in preset_files.items():
            for cfg in args.configs:
                for rep in range(1, args.reps + 1):
                    fut = pool.submit(run_pcsat, args.coar, cfg, smt_path, args.timeout, args.distro)
                    pcsat_futs.append((label, nk_path, pr, cfg, rep, csp, fut))

    katch_ref: dict[str, str] = {}
    for label, nk_path, _ in prepared:
        v, ms = run_nksynth(args.katch2, nk_path, args.timeout, args.distro)
        katch_ref[label] = v
        rows.append([label, "katch2", "-", "default", 1, v, ms, "", ""])
        print(f"katch2  {label:32} {'-':10} {'default':18} {v:8} {ms / 1000:7.2f}s", flush=True)

    for label, nk_path, pr, cfg, rep, csp, fut in pcsat_futs:
        v, ms, defs = fut.result()
        chk_note = ""
        ref = katch_ref.get(label)
        if ref in ("sat", "unsat") and v in ("sat", "unsat"):
            chk_note = "OK" if v == ref else "MISMATCH"
        if args.verify and v == "sat" and defs:
            try:
                nksol = pcsat_model_to_nksol(csp, defs)
                with tempfile.NamedTemporaryFile("w", suffix=".nksol", delete=False, encoding="utf-8") as tf:
                    tf.write(nksol)
                    sol_path = Path(tf.name)
                cv, _ = run_nksynth(args.katch2, nk_path, args.timeout, args.distro, check_sol=sol_path)
                sol_path.unlink(missing_ok=True)
                chk_note += f" [--check:{cv}]"
            except Exception as exc:
                chk_note += f" [skip-check:{exc}]"
        rows.append([label, "pcsat", pr, cfg, rep, v, ms, chk_note, translation_ms[label, pr]])
        print(
            f"pcsat   {label:32} {pr:10} {cfg:18} #{rep} {v:8} {ms / 1000:7.2f}s  {chk_note}",
            flush=True,
        )

    pool.shutdown()

    with args.csv.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["instance", "tool", "preset", "config", "rep", "verdict", "ms", "check", "translation_ms"])
        w.writerows(rows)
    print(f"\nSaved CSV: {args.csv}")


if __name__ == "__main__":
    main()
