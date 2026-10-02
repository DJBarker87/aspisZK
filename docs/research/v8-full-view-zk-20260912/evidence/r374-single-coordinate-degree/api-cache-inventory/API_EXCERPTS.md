# Pinned polynomial API excerpts

These statements were copied from the pinned Mathlib checkout at commit `9a04890da70b255c5e1b4da353fa697cf0dd3afe`. Full source files, paths, hashes, byte sizes, and `.olean` hashes are recorded in `inventory.json`.

`Mathlib/Algebra/Polynomial/BigOperators.lean:61-63`:

```lean
theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i ∈ s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
```

`BigOperators.lean:65-67` provides `natDegree_sum_le_of_forall_le`, which bounds a finite sum by `n` when each summand has natDegree at most `n`. `BigOperators.lean:136-137` provides:

```lean
theorem natDegree_prod_le : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
```

The pinned tree has no declarations named `natDegree_finset_prod` or `natDegree_finset_sum_le`. `Degree/Defs.lean:468` provides the binary bound `natDegree_mul_le`; `Degree/Operations.lean` imports `Degree.Defs`, but the finite-sum and finite-product bounds are in `BigOperators.lean`.

`Mathlib/Algebra/Polynomial/Eval/Defs.lean` declares `eval_C` at 283-284 and `eval_X` at 295-296. Finite-sum evaluation is `eval_finsetSum` at 348-350; `eval_sum` at 344-346 instead concerns the polynomial coefficient-sum operation. Finite-product evaluation is `eval_prod` at 675-677.

This is an API/source inventory only. No theorem was synthesized and no Lean compile or cache rebuild was run.
