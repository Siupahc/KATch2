# Hospital example: KATch2-synth vs PCSat (pfwCSP)

The synthesis problem of `hospital_test.pdf`: find the policy `X` of the core switch `S` so that
traffic for `W`, and non-FTP traffic for `M`, is delivered (N1), FTP never reaches `M` (N2),
and `S` only forwards (N3).

```
Internet -pt1-> G -2---1- S -2---1- M   (imaging, vulnerable FTP server)
                          S -3---1- W   (workstation)
                          S -4---1- I   (inspection)
```

Expected: `X = sw=S ; (dst=M ; typ!=ftp ; pt:=2 + dst=W ; pt:=3)`.

## Files

| file | tool | content |
|---|---|---|
| `hospital_wf.smt2` | PCSat | pdf section 4, literally: `X, R, D` + `W` free (`declare-wfp`), `exists p'` in a head, anti-spoofing on |
| `hospital_bfs.smt2` | PCSat | same, `W` fixed by BFS distances (pdf section 5) |
| `hospital_opt.smt2` | PCSat | same as `bfs`, with the structure pushed into the encoding (see below) |
| `hospital_nospoof.nksynth` | KATch2 | pdf section 2 + anti-spoofing: **same spec as the three `.smt2`** |
| `hospital.nksynth` | KATch2 | pdf section 2 literally: `X <= sw=S; T; sw:=S` (S may also rewrite `dst`/`typ`) |
| `hospital.expected.nksol` | KATch2 | the expected hole, for `nksynth --check` |
| `configs/*.json` | PCSat | CoAR's `pcsat_*` configs, with the solution printer switched on |
| `run_pcsat.sh` | | runs PCSat in WSL / Linux, prints `VERDICT MS` + the solution |
| `run_nksynth.sh` | | runs `nksynth` in WSL |
| `compare_hospital.py` | | runs everything, table + `results.csv` |

Why `.smt2` and not `.hes`: `.hes` is the muCLP format (MuVal / MuStrat), which checks the
validity of a fixed-point formula. It cannot say "**there exists** an `X`". The pfwCSP solver
(PCSat) reads `.smt2` (or `.clp`): `declare-fun` = unknown predicate, `declare-wfp` =
well-founded unknown, and `exists` in a clause head is skolemised by PCSat into functional
predicates (`FN_...`). Run it with `-p pfwcsp`.

Packets in the `.smt2`: 5 integers `(sw pt dst typ dir)`, with `G=1 S=2 M=3 W=4 I=5`,
`ftp=21`, `dir`: `in=0`, `out=1`. In the `.nksynth`: `sw=x[0..3] pt=x[3..6] dst=x[6..9]
typ=x[9..11]` (`ftp=1`). The hole is called `hS` because `X` is a keyword (LTL next) in KATch2.

### `hospital_opt.smt2`: what changes

1. N3 + anti-spoofing are built into the hole's arity: `X(pt, dst, typ, pt')` instead of
   `X(p, p')` over 10 integers (on `S` the hole can only choose the output port).
2. The known steps (`Pol0`, `Link`) are partial **functions**, so "there exists a known step to
   a `D` packet" becomes `HasKnown(p)` plus a universal clause: no existential there. The only
   existential left is the port chosen by `X` (1 skolem function instead of 5).
3. `W` is fixed by BFS (as in `bfs`).

All of these are sound and keep the expected solution. 1 and 2 can be done by the
translator in general: (1) from the hole shape, (2) whenever the fixed part of the network is
deterministic.

## Correctness checks done

* With z3, the expected solution of the pdf (`X`, `R`, `D` written by hand) satisfies every
  clause of `hospital_bfs.smt2` (`sat`).
* `nksynth hospital.nksynth --check hospital.expected.nksol` → `VALID` (same for
  `hospital_nospoof.nksynth`), and `hS = 0` → `INVALID`.
* The `X` that PCSat synthesises on `hospital_opt.smt2` is the expected one:
  `(dst=M ∧ typ≠ftp ∧ pt'=2) ∨ (dst=W ∧ pt'=3)`, with extra guards on the input port that
  change nothing.

## Results (2026-11-16)

### KATch2-synth, current version (after merging `mb64/synth` up to `c8aaef6`)

| file | result (5 runs, randomised solver) |
|---|---|
| `hospital_nospoof.nksynth` | **5/5 SAT in 8–11 ms**, every solution `VALID` under `--check` |
| `hospital.nksynth` | **5/5 SAT in 6–7 ms**, every solution `VALID` under `--check` |

The solutions are correct but not minimised: 1–3 KB of expression for `nospoof`, 30–90 KB
for the `T` version (the hole also does arbitrary things on packets that never reach it).

### KATch2-synth, old version (fork before the merge, `fd6dad2`)

Timeout on both files (300 s; no answer after ~25 min and 2.5 GB either). CEGIS iterations got
slower and slower (300 → 3 s, 1000 → 38 s, 2000 → 184 s). The blocking constraint was the
lower bound N1 through the star (N1+N3 alone: no answer in 120 s, SAT in 0.27 s with
`--no-clause-merge`). Fixed by Mark's optimisations.

### PCSat (300 s timeout, 4 runs per line, 12 in parallel)

| file | config | result |
|---|---|---|
| `hospital_opt.smt2` | `pcsat_tbq` | **4/4 sat**, median 132 s (85–217 s); earlier runs: 29 s to >240 s |
| `hospital_opt.smt2` | `pcsat_ppm_tbq_ar` | 1/4 sat (253 s) |
| `hospital_bfs.smt2` | both | 0/4 |
| `hospital_wf.smt2` | both | 0/4 |

Shorter runs (180 s) of `wf` / `bfs` with `pcsat_tb`, `tb_ar`, `tbq_ar`, `dt`, `dt_lazy`,
`dt_svm`: all timeouts.

## Building KATch2-synth

Since Mark switched to CaDiCaL (`rustsat-cadical`), `nksynth` no longer builds with MSVC
(CaDiCaL uses GCC `__attribute__`). Build it in WSL instead (needs `libclang-dev` for bindgen),
with a separate target directory so that it does not clash with the Windows one:

```bash
# in WSL
sudo apt install libclang-dev
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
cd /mnt/c/Users/<you>/Documents/GitHub/KATch2
CARGO_TARGET_DIR=~/katch2-target cargo build --release --bin nksynth
```

`compare_hospital.py` uses `wsl:~/katch2-target/release/nksynth` by default on Windows
(through `run_nksynth.sh`).

## Running

```bash
python compare_hospital.py                       # all, 300 s timeout, 3 PCSat runs per (file, config)
python compare_hospital.py --timeout 120 --reps 5 --configs pcsat_tbq_sol
python compare_hospital.py --only katch2 --timeout 60
```

PCSat is randomised: the same file can be solved in 30 s or time out after 240 s,
hence `--reps`.
