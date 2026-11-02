# MuStrat answers "invalid" on a valid fixed-point unfolding

CoAR commit `59017e6`, configuration `config/solver/mustrat.json`. Every query in this folder is
**valid**; every "invalid" below came out 3 times out of 3. Re-run with `bash run.sh [COAR_DIR]`.

## The NetKAT question

```
p = (f = 1; f := 2) + (f = 2; f := 3)        p* === 1 + p; p*  ?
```

This holds for **every** `p`: it is the definition of star. In μCLP, `p*` becomes a predicate
`S` and `1 + p; p*` becomes **exactly the body of `S`**, so the query is "`S` ⇔ the definition
of `S`", true for any fixed point. KATch2 and MuVal agree it is true.

## Files

| file | content | MuStrat | MuVal |
|---|---|---|---|
| `unfold_1field.nkt` → `unfold_1field.hes` | the check above, one field, naive encoding (`nkt.py`) | **invalid** | valid |
| `unfold_2fields.nkt` → `unfold_2fields.hes` | same plus a field `g` that `p` never touches | **invalid** | timeout |
| `minimal_fails.hes` | hand-reduced: 1 variable, no domain, only `S ⇒ body` | **invalid** | timeout |
| `minimal_passes.hes` | same formula with the `exists` distributed over the `\/` | valid | valid |

## The minimal pair

```
// minimal_fails.hes  — MuStrat: invalid (wrong)
forall (x: int) (y: int). S x y => (x = y \/ (exists (m: int). ((x = 1 /\ m = 2) \/ (x = 2 /\ m = 3)) /\ S m y))
s.t.
S (x: int) (y: int): bool =mu
  x = y \/ (exists (m: int). ((x = 1 /\ m = 2) \/ (x = 2 /\ m = 3)) /\ S m y);

// minimal_passes.hes — MuStrat: valid (right)
forall (x: int) (y: int). S x y => (x = y \/ (exists (m: int). x = 1 /\ m = 2 /\ S m y) \/ (exists (m: int). x = 2 /\ m = 3 /\ S m y))
s.t.
S (x: int) (y: int): bool =mu
  x = y \/ (exists (m: int). x = 1 /\ m = 2 /\ S m y) \/ (exists (m: int). x = 2 /\ m = 3 /\ S m y);
```

The two are logically identical: `∃m. (A ∨ B) ∧ C ≡ (∃m. A ∧ C) ∨ (∃m. B ∧ C)`.

## Other variants tried (not kept as files)

Still **invalid**: without the domain constraint; without the useless inner `exists k. x = k`
of the naive encoding; with 1 or 2 fields.
**Valid** again: a single branch (no `\/` under the `exists`); `m` replaced by its value (no
`exists`); the direct encoding of `nkt.py` (no `exists`); the membership query `S 1 3` with the
same `S`.

So the trigger is an **`exists` whose body contains a `\/`, next to the recursive call**, when
MuStrat has to prove `S ⇒ body of S`. MuStrat understands `S` itself (the membership is right).
MuVal never answers wrong; it only sometimes times out.
