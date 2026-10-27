# NetKAT → μCLP (MuVal / MuStrat)

Experiments: check NetKAT properties with a **fixed-point logic** solver (μCLP, the
[CoAR](https://github.com/hiroshi-unno/coar) tools by Hiroshi Unno) instead of KATch2, and
compare the two.

For now: **membership** and **equivalence / inclusion**, **without `dup`** and **without holes**.

| file | role |
|---|---|
| `nkt.py` | reads `.nkt` files, translates them to KATch2 (`.nksynth`) and to μCLP (`.hes`) |
| `compare.py` | runs KATch2 and the CoAR solvers on every check and compares them |
| `run_coar.sh` | small CoAR launcher (times the run inside WSL / Linux) |
| `examples/*.nkt` | the test cases |
| `bugs/` | wrong solver answers, reduced and reproducible (to report) |
| `out/` | generated files + `results.csv` (ignored by git) |

---

## 1. Reminder: what a (dup-free) NetKAT program means

A packet is a record of **fields**: `sw` (the switch the packet is at), `pt` (port),
`dst` (destination)… These are conventional names; KATch2 itself only knows bits
`x0, x1, …` and ranges `x[a..b]`.

A program `p` denotes a **relation** ⟦p⟧: the set of pairs (input packet, output packet)
it can produce.

| NetKAT | meaning |
|---|---|
| `sw = 1` | **test**: let the packet through unchanged if `sw` is 1, drop it otherwise |
| `sw := 2` | **assignment**: set `sw` to 2, leave the other fields alone |
| `p + q` | **union**: what `p` does **or** what `q` does (both outputs are possible) |
| `p ; q` | **sequence**: `p` then `q` |
| `p*` | **star**: `p` repeated 0, 1, 2, … times |
| `1` | do nothing (let everything through) — also the test "true" |
| `0` | drop everything — also the test "false" |
| `!a` | negation of a **test** |

The two questions:

* **membership**: is the given pair `(π_in, π_out)` in ⟦p⟧?
  ("can this packet come out like that?")
* **equivalence** `p ≡ q`: ⟦p⟧ = ⟦q⟧, for **all** pairs of packets;
  **inclusion** `p ≤ q`: ⟦p⟧ ⊆ ⟦q⟧.

---

## 2. Translation to μCLP

### 2.1 A program becomes a predicate over two packets

Every field becomes an integer argument, once for the input (`i_…`) and once for the output
(`o_…`). With fields `sw` and `pt`, a program `p` becomes

```
P (i_sw: int) (i_pt: int) (o_sw: int) (o_pt: int): bool
```

read "`p` can turn `(i_sw, i_pt)` into `(o_sw, o_pt)`".

### 2.2 Rules (literal translation, `naive` encoding)

Write ⟦p⟧(x, y) for "the formula saying that `p` turns `x` into `y`".
Example with the two fields `sw`, `pt`:

| NetKAT | μCLP formula ⟦p⟧(x, y) |
|---|---|
| `1` | `x_sw = y_sw /\ x_pt = y_pt` |
| `0` | `false` |
| `sw = 1` | `x_sw = y_sw /\ x_pt = y_pt /\ x_sw = 1` |
| `sw != 1` | `x_sw = y_sw /\ x_pt = y_pt /\ x_sw != 1` |
| `sw := 2` | `y_sw = 2 /\ x_pt = y_pt` (the other fields are copied) |
| `p + q` | `⟦p⟧(x, y) \/ ⟦q⟧(x, y)` |
| `p ; q` | `exists (m_sw: int) (m_pt: int). ⟦p⟧(x, m) /\ ⟦q⟧(m, y)` (`m` = intermediate packet) |
| `p*` | a **named predicate**, defined as a **least fixed point**: see below |

Compound tests: `a + b` → `\/`, `a ; b` → `/\`, `!a` → negation (De Morgan).

### 2.3 Star: the only case that needs a fixed point

```
Star (i_sw: int) (i_pt: int) (o_sw: int) (o_pt: int): bool =mu
     (i_sw = o_sw /\ i_pt = o_pt)                                   // 0 steps
  \/ (exists (m_sw: int) (m_pt: int). ⟦p⟧(i, m) /\ Star m_sw m_pt o_sw o_pt);   // one step of p, then p*
```

and, wherever `p*` occurs: `Star x_sw x_pt y_sw y_pt`.

**`=mu` is mandatory.** μ = the *least* set satisfying the equation = exactly the pairs
reachable in a **finite** number of steps. With `=nu` (the greatest), a loop "justifies
itself": in `examples/03_toggle.nkt`, `0 → 5` would become true.

### 2.4 `direct` encoding (fewer `exists`)

Same meaning, formulas that are easier for the solver. A **star-free** part (tests and
assignments) is executed symbolically: the output packet is computed directly instead of being
introduced by an `exists`.

```
(sw = 1; pt := 2) + (sw = 2; pt := 2)     ⇒    (if x_sw = 1: output (1, 2))  or  (if x_sw = 2: output (2, 2))
```

so, for `net = (pol; topo)*` on a line of 3 switches:

```
Star1 (i_sw: int) (i_pt: int) (o_sw: int) (o_pt: int): bool =mu
  (i_sw = o_sw /\ i_pt = o_pt) \/ (i_sw = 1 /\ Star1 2 1 o_sw o_pt) \/ (i_sw = 2 /\ Star1 3 1 o_sw o_pt);
```

Rules used by `nkt.py --encoding direct`:

* a star-free expression = a list of "guard ⇒ output packet" (a normal form);
* after a test `sw = 1`, `sw` is replaced by the constant 1 (contradictory branches vanish);
* `p ; q` with a star-free `p`: the output of `p` is substituted into `q` (no `exists`);
* `p ; test`: the output is tested directly (no `exists`);
* otherwise (a star on the left of a `;`), an `exists` is kept.

On the hand-written equivalence of `02_line.nkt`: `naive` → timeout (> 60 s) with MuVal,
`direct` → 0.4 s. **The choice of encoding is the heart of these experiments.**

### 2.5 Queries

| question | query |
|---|---|
| membership `(π_in, π_out) ∈ p` | `⟦p⟧(π_in, π_out)` with constants, e.g. `Star1 1 0 3 1` |
| equivalence `p ≡ q` | `forall (i…) (o…). (domain) => (⟦p⟧(i, o) <=> ⟦q⟧(i, o))` |
| inclusion `p ≤ q` | `forall (i…) (o…). (domain) => (⟦p⟧(i, o) => ⟦q⟧(i, o))` |

* **Domain.** μCLP integers are unbounded, whereas a `w`-bit NetKAT field ranges over
  `0 … 2^w − 1`. Without the constraint `0 <= i_sw /\ i_sw <= 3 /\ …`, laws that hold in
  NetKAT become false: `f = 0 + f = 1 + f = 2 + f = 3 ≡ 1` (see `01_axioms.nkt`).
* **Negation.** `=>` and `<=>` use the complement of `Star`. CoAR builds it by itself: a
  predicate `Star1_neg` defined with `=nu` (De Morgan: μ↔ν, ∃↔∀, ∨↔∧). To see it:
  `main.exe -c ./config/solver/printer.json -p muclp file.hes`.
* **At least one predicate.** The `.hes` grammar requires at least one equation after `s.t.`;
  without any star, `nkt.py` adds a useless predicate `Unused`.

### 2.6 `.hes` syntax in short

```
<query>
s.t.
Name (x: int) (y: int): bool =mu <body>;      // least fixed point
Other (x: int): bool =nu <body>;              // greatest fixed point
```

`/\`, `\/`, `not`, `=>`, `<=>`, `exists (x: int).`, `forall (x: int).`, `=`, `!=`, `<=`, `<`,
`+`, `-`. Application is written `P x 3 (y + 1)`. Comments `/* … */` or `//`.
The real reference: `lib/muCLP/parser.mly` in CoAR, and the examples in
`benchmarks/muCLP/simple/`.

---

## 3. The `.nkt` format

```
field sw 2                                   // field sw on 2 bits (values 0..3)
field pt 2
def pol  = (sw = 1; pt := 2) + (sw = 2; pt := 2)
def net  = (pol; topo)*
member through: (sw=1, pt=0) -> (sw=3, pt=1) in net
equiv  summary: sw = 1; pt = 0; net; sw = 3 === sw = 1; pt = 0; sw := 3; pt := 1
incl   isolated: sw = 3; net; sw = 1 <= 0
```

* tests `f = v` (or `f == v`), `f != v`; assignments `f := v`; `+`, `;`, `*`, `!`, `0`, `1`,
  parentheses; precedence: `*` > `;` > `+`;
* a `member` packet must give **all** fields;
* a statement may span several lines; comments `//` or `#`.

For KATch2, every field becomes a bit range, in declaration order
(`sw` → `x[0..2]`, `pt` → `x[2..4]`), and every check an `assert`:
`member` becomes `(tests of the input ; assignments of the output) <= p`.

---

## 4. Installation

### Windows + WSL (current setup)

* KATch2: `cargo build --release` at the repository root (Windows side), with `libz3.dll` on
  the `PATH`.
* CoAR in WSL (Ubuntu): `opam switch create 5.4.0`, then in `~/coar`:
  `opam install . --deps-only && dune build main.exe`
  (system packages: `libblas-dev liblapack-dev libmpfr-dev libglpk-dev libgmp-dev libffi-dev pkg-config`).
* `compare.py` runs on the Windows side and calls CoAR through `wsl.exe`
  (options `--coar ~/coar` and `--distro Ubuntu`).

### Arch Linux (not tested yet)

```bash
sudo pacman -S --needed base-devel git python rustup z3 opam \
                         blas lapack mpfr gmp glpk libffi pkgconf
rustup default stable

# KATch2 (links against the system libz3.so)
cd KATch2 && cargo build --release

# CoAR
opam init                      # first time only
opam switch create 5.4.0
eval $(opam env --switch=5.4.0)
git clone https://github.com/hiroshi-unno/coar ~/coar
cd ~/coar && opam install . --deps-only && dune build main.exe
```

`opam install` rebuilds Z3's OCaml bindings, which takes a while. CoAR's README asks for a
C++ compiler with `<format>` (GCC ≥ 13), which current Arch has. On Linux, `compare.py` calls
`run_coar.sh` directly, so there is nothing else to configure.

## 5. Running

```bash
cd muclp
python compare.py                                    # all examples, MuVal + MuStrat, direct + naive
python compare.py examples/02_line.nkt --timeout 10
python compare.py --solvers muval --encodings direct
python nkt.py examples/02_line.nkt                   # print the translations without running anything
```

Reading the table: `true` / `false` = verdict, then the time; ✓ / ✗ = agreement /
disagreement with KATch2 (the oracle); `timeout` and `unknown` are not errors, the solver just
did not conclude in time. CoAR times are measured inside WSL / Linux (without the `wsl.exe`
start-up); KATch2 times include process start-up.

---

## 6. First results (32 checks, 20 s timeout)

| | correct | timeout | wrong |
|---|---|---|---|
| MuVal, `direct` | **32** | 0 | 0 |
| MuVal, `naive` | 27 | 5 | 0 |
| MuStrat, `direct` | 30 | 2 | 0 |
| MuStrat, `naive` | 29 | 2 | **1** |

* KATch2 answers everywhere in ~0.02 s. MuVal costs at least ~0.13 s (start-up), up to ~3 s on
  equivalences with a star.
* The `direct` encoding is clearly better: all of MuVal's timeouts are with `naive`.
* MuStrat answers "invalid" on a valid query (`bugs/mustrat_invalid_unfold.hes`) and does not
  conclude on the ARPANET membership checks.

## 7. Not supported yet

`dup` (traces), holes (synthesis), KATch2-specific operators (`&`, `^`, `-`, `~` complement,
`T`), bit patterns (`x[0..8] ~ 10.0.0.0/8`), counterexamples (CoAR only says `invalid`).
