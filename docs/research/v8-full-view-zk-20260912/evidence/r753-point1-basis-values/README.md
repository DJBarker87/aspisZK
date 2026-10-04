# R753 point-1 finite basis emitter (review plan)

`emit_point1_basis.rs` remains uncompiled and unrun. It uses only Rust `std`,
including its local SHA-256 routine. It accepts either `--emit`, which refuses
to overwrite the requested output directory, or `--check`, which regenerates
the same text in memory and requires an existing directory to match the exact
seven chunk files and manifest byte for byte.

A future invocation must supply an explicit source revision and exact SHA-256
of the checked R748 JSON plan:

```sh
rustc -O emit_point1_basis.rs -o emit_point1_basis
./emit_point1_basis --emit \
  --repo /Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922 \
  --plan .r21-scratch/r748-chosen222-point1-leaf-plan.json \
  --expected-plan-sha <exact-plan-sha256> \
  --out-dir .r21-scratch/r753-point1-basis-generated \
  --source-revision <git-revision>
./emit_point1_basis --check <the same arguments>
```

The emitter validates the five plan pins, including the exact green R748
source, and the plan shape of 196 strictly ascending original indices in
768..1022. It writes seven Lean chunks of at most 32 named lemmas. Every
lemma rewrites the existing R748 `point_eq_p`, reduces exactly the ten
`sourcePointBasis` factors with `norm_num [...] <;> decide`, and immediately
prints its axioms.

The 323 guard-zero leaves remain for generic R752 support. The shared pivot
1023 is deliberately not duplicated: the generated manifest references the
existing `AspisR19.R754Point1GuardedTransport.point1_pivot_basis` and
`point1_pivot_basis_neg` proof, with its source SHA. No source chord, matrix,
rank, witness relation, compilation, or generated Lean execution occurs here.
