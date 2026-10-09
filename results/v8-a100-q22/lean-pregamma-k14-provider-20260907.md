# V8 fallback-free pre-gamma K1.4 provider evidence

Source revision tested before the milestone commit: `0276264f514c01ac293e3db1df3d1698e5a551a2` plus the subsequently committed source diff in `68a74c7b`.

All commands were focused single-module Lean invocations.  Every process stayed below the user's 8 GiB per-job limit and reported zero swap.

## Failure ladder

The first direct V8 build failed because a transitive V7 object was absent:

```text
lake env lean AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean
AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean:1:0: error:
object file '.../V7Tag73CheckedRefinementFullFutureFreePath.olean' ... does not exist
exit 1; 8.12 s; max RSS 1,188,610,048 bytes; swaps 0
```

Two attempted predecessor rebuilds exposed source/cache mismatches rather than a V8 theorem error:

1. The research-tree predecessor reached an impossible `tape : DeployedFixedTape ⊢ False` goal at line 2485 and contaminated downstream declarations with `sorryAx`; exit 1, 19.96 s, max RSS 5,629,083,648 bytes, swaps 0.
2. The newer main-tree source failed at the shifted transcript tail, including the missing `queryBatch` binding-event equality at line 2696; exit 1, 16.54 s, max RSS 5,614,567,424 bytes, swaps 0.

Neither failed build is counted as a formal result.  A concurrently changing main cache was isolated by copying the clean, matching V7 activation object set into the research worktree's ignored `.lake` overlay.  No tracked source was overwritten.

## Successful focused builds

```text
/usr/bin/time -l lake env lean \
  -o .lake/build/lib/lean/AspisFormal/K1/V8A100PreGammaTupleBinding.olean \
  AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean
```

- exit: 0
- wall: 40.20 s
- max RSS: 4,232,740,864 bytes
- swaps: 0

```text
/usr/bin/time -l lake env lean \
  -o .lake/build/lib/lean/AspisFormal/K1/V8A100SchedulerNativeK14Provider.olean \
  AspisFormal/AspisFormal/K1/V8A100SchedulerNativeK14Provider.lean
```

- exit: 0
- wall: 23.85 s
- max RSS: 4,895,948,800 bytes
- swaps: 0

Every printed declaration in both modules reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, new axiom, opaque unproved constant, or `unsafe` escape is used.

## Result and boundary

The source replay now constructs `gamma -> Option (RestoredK14Branch ...)` directly and derives the matching K1.3 selected-branch view without fabricating a fallback extraction for unavailable gammas.  This closes the provider-interface defect.

It does **not** prove that Rust's two scalar gamma-dot checks imply equality of all 58 component evaluations.  That implication is false.  The release path needs the separate scalar-fingerprint bad-gamma theorem and an actual V8 parser/transcript refinement.
