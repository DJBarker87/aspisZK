# Point-row model to exact dual-fold dot handoff

Status: the point model identities are checked. The 100-bit target is not yet
established. Root owns application to the accepted caller and final release
composition; no Rust source, protocol, runtime gate or security contract changed.

## Accepted API

Import `S9PointRowDualFoldModelV1`; it imports the separate
`S9PointRowTwoFoldV1` predecessor. Both use namespace
`AspisR1S9PointRowDualFoldModelV1`.

- `rawRow model k : Fin 1024 → ExactQM` is the five-factor constructor-row model.
- `rawRow_children` gives the exact symbolic radix-four child product.
- `factor_model_eq` matches the actual source scalar factor polynomial, including
  PERM and QUARTER, to the precise generic model factor.
- `point_row_two_dual_folds` identifies two dual folds with the product of the
  two source scalar factors and the remaining model high product.
- `rowValue_eq_two_dual_dot model k a0 a1 f` identifies the existing `rowValue`
  with the dot against the SAME source-buffer `fieldValue f` vector and those
  two folds. It adds no canonicality, source-call, input-vector or output-meaning
  premise.

The vector uses exactly:

```
fun i : Fin 64 =>
  AspisR1S9SharedSumObservationsV1.fieldValue f
    (AspisR1S9SharedSumObservationsV1.finIndex
      AspisR1S9SharedHighConstructorModelV1.rowValue._proof_1 i)
```

Choose this `h64` when applying Factor's parameterized
`stored_inactive_common_input` / `stored_private_common_input` and Pair's
same-input interfaces. Do not compare a completed sum against a new `by decide`
instance: the actual index is unchanged (`finIndex_val = i.val`), but a different
opaque proof argument triggered elaborator reduction. The old candidate was
unproved; no accepted statement was silently replaced. This is proof-evidence
selection, with no input/adversary restriction.

## Exact focused outputs

Two-fold source SHA:
`ac0618b4df5676b7617bf55ad65c07ab3443da2a015da66ab80f88a67726fc5c`.
Object: `bd15f0ed9d19730d18403be206878cb465dbba5b7afd9e5945ca8904cbf11cfa`.
Workspace: `/tmp/a3-s9-point-row-two-fold-v9-alias-delta-check-20261024`.
Exit 0, 23.162 s, peak aggregate RSS 3,294,904,320 bytes, zero swap, std3.

Final dot source SHA:
`9ec965fe0b261772a294b5c599e97bceca69747781b7944fca3cf904f9a7064c`.
Object: `0f6f176c8a5a9fc105f61b3c3ffd801ca0b7c1d4cc6b06cccd955d6b6b4a5d69`.
Workspace: `/tmp/a3-s9-point-row-dot-v12-high-alias-check-20261024`.
Exit 0, 26.537 s, peak aggregate RSS 3,253,403,648 bytes, zero swap, std3.
Use the final workspace's `profile.txt`, with its own `objects` prepended. Add the
accepted two-fold objects as already selected in that profile. No library build
or unchanged replay is needed for the next consumer.

## Source-only packets (all checkers PASS)

Under `docs/research/100bit-spend-path-20261013/evidence/`:

1. `s9-point-opaque-operator-transports-v1-20261024`
2. `s9-point-native-field-projection-transports-v1-20261024`
3. `s9-point-row-two-fold-model-v1-20261024`
4. `s9-point-row-source-observation-dual-dot-v1-20261024`

Each manifest pins exact source, status, wall time, RSS, swap, revision and axioms.
Rejected actual checks and raw Expr diagnostics are retained and classified.
The new generic quadratic multiplication API was tested before native operands;
then exact-context triple/sum interfaces, then the two-fold and dot consumers.
The final repair expands only assigned local types, named transparent E aliases,
and our thin `highProduct` abbreviation. The underlying table highProduct,
source fieldValue/readers, and 64/1024 concrete rows remain opaque.

## Scope and next composition

This is a model identity over the actual source observation function. Successful
source reads, one same-execution constructor model, actual stored part values,
and original parts/k provenance come from the separately checked source caller
interfaces. Apply these APIs to Root's ORIGINAL compared caller's parts and
Trace, not separately chosen existential vectors. Pair's public D18/circle
functionals and Factor's raw0/4 meanings are ready for that composition.

OtherOps installation/source-cut boundaries, exact public relation/experiment
transport, ABI/runtime/artifact binding, coherent final closure replay, and the
complete security bound remain explicit. No full security or release closure
is claimed by these mathematical identities.
