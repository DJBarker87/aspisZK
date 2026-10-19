# Identical associated-type loop matcher

Status: the unchanged normalized library initialization loop passes strict
symbolic borrow-checking. Full Rust-library source admission remains OPEN.
Production Rust and all 85 previously checked Lean targets remain unchanged.

The ordinary branch-joining path reproduces the two-iteration failure, so the
opt-in no-branch-join fallback is not its cause. A focused fixed-point trace
shows that both successive contexts have the same guard/borrow shape modulo
fresh IDs. The strict nonrecovering match reports:

```
Distinct("match_rtys:\n- ty0: TraitClause0::Output\n- ty1: TraitClause0::Output")
```

The pinned `InterpMatchCtxs.match_types` has no TTraitType case. It recursively
matches the Guard/slice/MaybeUninit types, reaches the identical associated
Output projection and calls match_distinct_types. The loop is therefore
rejected despite equality at that leaf. Increasing the iteration count would
not address this missing equality case; no iteration limit was changed.

An isolated copy of the previously pinned frontend adds one opt-in case:

```
| TTraitType _, TTraitType _
  when Sys.getenv_opt "AENEAS_IDENTICAL_ASSOCIATED_TYPES" = Some "1"
       && phys_eq ty0 ty1 && ty_no_regions ty0 -> ty0
```

Only physically identical, region-free projections take the case. There are
no regions needing registration or alpha-renaming at this leaf. Different
projections and projections containing any region retain the existing path.
No type, borrow, copy, sanity or fixed-point check is disabled. This is a
frontend repair in the existing trusted translation boundary, not a new Lean
axiom, a new protocol premise, or an equivalence theorem by itself. The earlier
LLBC dereference rewrite remains experimental and separately needs semantic
justification or replacement.

The frontend is built in a fresh copied workspace; neither previously pinned
frontend is edited. Source/patch/binary hashes and exact source changes are
frozen in `associated-types-diagnostic-a/build`. The build is incremental,
optimized OCaml with one Dune job. Its actual Docker cgroup is verified at
memory.high=6GiB, memory.max=8GiB, swap.max=0 before the compile gate opens.
The outer controller also has a separate capped scope. Reservations including
the new compile cap total 40.375GiB, below the 50GiB safe limit. Compilation
uses 10.39 seconds, peak RSS 502428KiB and zero process/cgroup swap.

`array-loop-associated-types-a` passes the exact selected normalized library
loop with `-checks -abort-on-error -borrow-check`; wall0.602s, RSS89232KiB,
zero swap. The projection makes other function bodies opaque only for this
diagnostic; every signature/type/trait and the selected declaration are
unchanged, with hashes recorded. This is successful symbolic borrow-checking,
not a successfully emitted or compiled Lean theorem. #print axioms is N/A.

The 14-case paired regression runs with matching disabled and enabled:

* Four pinned small baseline emissions in both modes remain byte-identical.
* The normalized dereference control remains byte-identical in both modes.
* The original unsupported mutable-copy example remains rejected in both.
* The exact isolated library loop retains the old mismatch with the option
  disabled and passes with it enabled.

All cases retain extensive sanity checks and have separate exact commands,
revision/features, exits, wall time, RSS and swap receipts. They pass in the
single capped `associated-types-regression-a` run. These tests establish this
scoped compatibility evidence; they are not a whole-frontend soundness proof.

The full normalized library emission, with both opt-in frontend repairs,
still exits1 (`array-associated-types-emission-a`, wall5.412s, RSS142032KiB,
zero swap). Mutable-copy and fixed-point errors are absent. The remaining
failures are the generic Try::from_output input-type mismatch and the backend
Try metadata having one parent where the current Rust trait has two, followed
by the resulting unresolved dictionary identifiers/recursive implementations.
No partial declaration with an unresolved identifier is promoted or imported.

Charon's expand_associated_types pass already documents two relevant limits:
recursive associated-type families are partly skipped, and trait-implementation
uniqueness is not used to infer equalities between repeated trait predicates.
The library's ChangeOutputType/Residual/Try family reaches this boundary.
Next work is to establish the required associated-projection equalities and a
coherent source interpretation of the newer dictionary family, preserving all
Rust constraints. Simply deleting the new Residual parent or accepting unequal
input types is not an admissible repair.

`check-associated-type-evidence.py` validates the source patch, build caps,
receipts, selected-loop projection and all paired controls without rerunning
unchanged builds. The complete 8.1MB fixed-point trace stays on the NUC and in
ignored scratch; the manifest pins its hash and a byte-exact 3050-byte excerpt.
The local focused matcher diagnostic and its exception trace are retained in
full. An initial diagnostic CLI construction error is archived separately and
is not counted as compiler or proof evidence.
