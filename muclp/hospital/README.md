# Hospital example: KATch2-synth vs PCSat (pfwCSP)

The synthesis problem: find the policy `X` of the core switch `S` so that traffic for `W`, and
non-FTP traffic for `M`, is delivered (N1), FTP never reaches `M` (N2), and `S` only forwards
(N3).

```
Internet -pt1-> G -2---1- S -2---1- M   (imaging, vulnerable FTP server)
                          S -3---1- W   (workstation)
                          S -4---1- I   (inspection)
```

Expected: `X = sw=S ; (dst=M ; typ!=ftp ; pt:=2 + dst=W ; pt:=3)`.

## Files

| file | tool | content |
|---|---|---|
| `hospital_wf.smt2` | PCSat | `X, R, D` + `W` free (`declare-wfp`), `exists p'` in a head, anti-spoofing on |
| `hospital_bfs.smt2` | PCSat | same, `W` fixed by BFS distances |
| `hospital_opt.smt2` | PCSat | same as `bfs`, with the structure pushed into the encoding (see below) |
| `hospital_generic.smt2` | PCSat | generic translation: relations on `(p, p')`, `W_` free (times out) |
| `hospital_nospoof.nksynth` | KATch2 | N1–N3 + anti-spoofing: **same spec as the three `.smt2`** |
| `hospital.nksynth` | KATch2 | N1–N3 with `X <= sw=S; T; sw:=S` (S may also rewrite `dst`/`typ`) |
| `hospital.expected.nksol` | KATch2 | the expected hole, for `nksynth --check` |
| `configs/*.json` | PCSat | CoAR's `pcsat_*` configs, with the solution printer switched on |
| `run_pcsat.sh` | | runs PCSat in WSL / Linux, prints `VERDICT MS` + the solution |
| `run_nksynth.sh` | | runs `nksynth` in WSL |
| `compare_hospital.py` | | runs everything, table + `results.csv` |

Packets in the `.smt2`: 5 integers `(sw pt dst typ dir)`, with `G=1 S=2 M=3 W=4 I=5`,
`ftp=21`, `dir`: `in=0`, `out=1`. In the `.nksynth`: `sw=x[0..3] pt=x[3..6] dst=x[6..9]
typ=x[9..11]` (`ftp=1`).

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

* With z3, the expected solution (`X`, `R`, `D` written by hand) satisfies every clause of
  `hospital_bfs.smt2` (`sat`).
* `nksynth hospital.nksynth --check hospital.expected.nksol` → `VALID` (same for
  `hospital_nospoof.nksynth`), and the empty hole (`0`) → `INVALID`.
* The `X` that PCSat synthesises on `hospital_opt.smt2` is the expected one:
  `(dst=M ∧ typ≠ftp ∧ pt'=2) ∨ (dst=W ∧ pt'=3)`, with extra guards on the input port that
  change nothing.

## Results (2026-11-16)

### KATch2-synth, current version (`6a8aa1e`)

| file | result (5 runs, randomised solver) |
|---|---|
| `hospital_nospoof.nksynth` | **5/5 SAT in 8–11 ms**, every solution `VALID` under `--check` |
| `hospital.nksynth` | **5/5 SAT in 6–7 ms**, every solution `VALID` under `--check` |

The solutions are correct but not minimised: 1–3 KB of expression for `nospoof`, 30–90 KB
for the `T` version (the hole also does arbitrary things on packets that never reach it).

### KATch2-synth, previous version (`fd6dad2`)

Timeout on both files (300 s; no answer after ~25 min and 2.5 GB either). I first forgot to `git pull` to get the latest version, so I thought PCSat was faster, but the current optimized version is miles ahead.

### PCSat (300 s timeout, 4 runs per line, 12 in parallel)

| file | config | result |
|---|---|---|
| `hospital_opt.smt2` | `pcsat_tbq` | **4/4 sat**, median 132 s (85–217 s); earlier runs: 29 s to >240 s |
| `hospital_opt.smt2` | `pcsat_ppm_tbq_ar` | 1/4 sat (253 s) |
| `hospital_bfs.smt2` | both | 0/4 |
| `hospital_wf.smt2` | both | 0/4 |
| `hospital_generic.smt2` | both | 0/4 |

Shorter runs (180 s) of `wf` / `bfs` with `pcsat_tb`, `tb_ar`, `tbq_ar`, `dt`, `dt_lazy`,
`dt_svm`: all timeouts.

### Candidate atoms on the generic encoding

CoAR (`59017e6`) accepts SMT-LIB `set-info :candidates` declarations as optional
qualifiers for individual unknowns. The generator below adds only these declarations.
The generic clauses, anti-spoofing constraint, eight existential integers and free
well-founded relation are identical across profiles.

* `structural` offers field equalities and local tests on switches, ports and FTP.
* `witness` offers one whole formula per unknown: a forwarding policy for `X`,
  the FTP safety invariant for `St`, identity plus the required paths for `D`,
  and the order G → S → {M, W} for `W_`. This is a diagnostic using the known
  solution. With those definitions substituted, Z3 checked the negations of all
  eight clauses as unsatisfiable. The order separately admits ranks 2, 1 and 0.
* `projected` strengthens the same safety invariant to cover every ingress port
  on G. Under TBQ, the qualifier trace shows that preprocessing removes the original
  compound atom for `St`, while the projected atom and the progress atom survive.
  The trace lists no declared qualifiers for `X` or `D` in either case.

At 300 s, both TBQ and PPM/TBQ/AR timed out twice on each of the baseline,
structural and witness inputs (12 concurrent runs). A single TBQ run with
the projected hint also timed out. With preprocessing disabled, TBQ kept the
original `St` hint, but both the baseline and witness profile still timed out
(one run each). Thus none of the 10 hinted runs returned a model within budget.
To reproduce under WSL,
from this directory:

```bash
for p in structural witness projected; do
  python3 hospital_candidates.py "$p" > "/tmp/hospital_$p.smt2"
done
python3 compare_hospital.py --only pcsat --smt2 hospital_generic.smt2 \
  /tmp/hospital_structural.smt2 /tmp/hospital_witness.smt2 \
  --configs pcsat_tbq_sol pcsat_ppm_tbq_ar_sol --reps 2 --jobs 12 \
  --timeout 300 --csv candidates_results.csv
python3 compare_hospital.py --only pcsat --smt2 hospital_generic.smt2 \
  /tmp/hospital_witness.smt2 --configs pcsat_tbq_nopre_sol --reps 1 --jobs 2 \
  --timeout 300 --csv candidates_nopre_results.csv
python3 compare_hospital.py --only pcsat --smt2 /tmp/hospital_projected.smt2 \
  --configs pcsat_tbq_sol --reps 1 --timeout 300 --csv candidates_projected_results.csv
```

### Eliminating existential packet witnesses

In the generic lower-star clause, `q` and `r` account for eight existential
integers. N3 keeps `X` on S, anti-spoofing preserves destination and type,
and each outgoing port has one cable. Thus only the choice of port at S is
free. Substituting the cable endpoints gives two equivalent rewrites of this
clause. Z3 checked both directions for arbitrary relations satisfying the
hole restrictions. All experiments used CoAR's PCSat with a 300 s limit.

| Input | Lower-star encoding | Observed outcome |
|---|---|---|
| `hospital_generic.smt2` | Two packet witnesses, recursive D and free W_ | 4/4 timed out |
| `hospital_generic_oneexists.smt2` | One port witness, next hop selected with ITEs | Four concurrent runs stopped manually at 44 s under memory pressure. A TBQ retry under a 4 GiB address-space limit exhausted memory at 230 s. |
| `hospital_generic_noexists.smt2` | Six explicit transitions, recursive D and free W_ | 4/4 timed out |
| `hospital_generic_factored.smt2` | Port cases factored through one ordinary predicate, Usable | Both runs killed under memory pressure (TBQ with and without preprocessing) |
| `hospital_paths.smt2` | Exact simple paths for N1, ordinary X and recursive St for N2 | TBQ 2/2 SAT (8.6, 16.3 s), PPM/TBQ/AR 2/2 SAT (68.7, 116.2 s) |

The last rewrite preserves the admissible policies for this hospital. For
fixed destination and type, ingress reaches S on port 1. A trip through G
returns to S:1, while a trip through I returns to S:4. M and W are terminal.
Deleting repeated states leaves either a direct exit or one detour through I.
Both cases are allowed. An independent graph traversal agreed with the path
formula for both exits and all 256 subsets of the eight relevant forwarding
choices. Three further TBQ runs in isolation all returned SAT (7.96, 8.17
and 11.78 s). Z3 checked all seven returned policies against the two delivery
requirements, the FTP prohibition, and the hole restrictions.

The first experiments overlapped and experienced memory pressure. In
`exists_results.csv` the four manually stopped runs are recorded as
`error`. To run the successful variant by itself from this directory:

```bash
python3 compare_hospital.py --only pcsat --smt2 hospital_paths.smt2 \
  --configs pcsat_tbq_sol --jobs 1 --reps 3 --csv exists_paths_serial.csv
```

## Running

```bash
python compare_hospital.py                       # all, 300 s timeout, 3 PCSat runs per (file, config)
python compare_hospital.py --timeout 120 --reps 5 --configs pcsat_tbq_sol
python compare_hospital.py --only katch2 --timeout 60
```

PCSat is randomised: the same file can be solved in 30 s or time out after 240 s,
hence `--reps`.
