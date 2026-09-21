# Consumed-weight workspace for the compact terminal

R34/R35 source base 2c03cc7b5dad76d731ae0628eef233b98eb034b1 plus this changeset.
R35 repairs the R33 terminal allocation regression without a heap increase or
a new transcript profile, but regresses primary CU against R28. It is not a
full privacy or source-extraction theorem.

## Ownership and bounded storage

After expanded weights have been absorbed, the primary ordinary accumulator
contains one Dense vector. The staged core adds a research-cfg-only ownership
accessor, into_single_dense_for_workspace, which moves that vector out without
copying or allocating and returns None for other component shapes. The actual
prepare constructor establishes the singleton Dense shape; the verifier maps
an unexpected shape to Error::Shape. Reference verification and prover access
take their unchanged paths. Production crates/aspis-core/src/sumcheck.rs is
untouched; its SHA256 remains
7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead.

The primary verifier replaces its old accumulator with the same query-only
eight-variable accumulator, retains the moved 1024-entry vector, and borrows
it at the terminal. Its old contents are no longer used. Safe split_at_mut
borrows divide the workspace into disjoint regions:

| Region | QM31 indices | Use |
| --- | --- | --- |
| Delta | 0..478 | Changed-prefix weights, then in-place permutation difference |
| Factors | 479..638 | Two 16+64 tensor-factor tables |
| Group sums | 639..766 | 64 normal/carry pairs, reused for prefix and binary-mask contractions |
| Unused | 767..1023 | Not read by this evaluator |

All used values are written before being read. The tensor formulas, fused
blocks, cycle traversal and weighted contraction are the R33 formulas; only
their storage changes. prefix_into and binary_masks_into overwrite caller
storage rather than collecting Vecs. The public carry-edge iterator follows
the same row/bit/half-scale transitions as the retained Vec routine; the old
routine remains a host reference. Both iterator exhaustion calls return None.
No coefficient-dependent work selection or mask resampling is introduced.

Expanded transcript bytes, claim/interpolant subtraction, source challenges,
image residuals, G channel, fresh-query injection, opening checks and the
complete dense reference verifier are retained. The helper uses the source
map already initialized by prepare; lazy map initialization is not claimed
allocation-free in isolation.

## Focused source/allocation controls

The new gate reuses the exact DenyWhileArmed allocator from the earlier R17
workspace probe, extracted and source-pinned by the stager. It passes:

- All 64 public edge schedules and repeated exhaustion match the old Vec routine.
- 32 complete compact terminals match both R33 and the actual dense source
  chord/four-fold pipeline, including zero, one, maximal limbs and degenerate
  public parameters. Consumed dirty buffers retain their pointer and capacity.
- The entire ownership handoff and terminal run with allocation denied:
  zero allocation attempts in all 32 cases.
- 256 prefix and 32 binary-mask workspace cases match allocating references,
  with zero allocation attempts. Empty, geometric-only and double-Dense
  accumulator shapes are rejected by the ownership accessor.

Release gate exit 0, wall 29.90 s (29.88 compilation), peak RSS 537136 KiB,
swaps 0; 4G/6G/zero-swap scope, TasksMax=128. The first compile failed on an
inner doc comment in an include! fragment (exit 101, 27.24 s, RSS 535928 KiB,
swaps 0); changing it to a plain comment fixed the source error. That failed
log is retained. No resource cap was raised.

The actual honest host proof accepts through both paths: exit 0, wall 11.69 s
(11.65 compilation), RSS 449032 KiB, swaps 0. The existing G-final mutation
is rejected: exit 0, reported 0.00 s, RSS 3344 KiB, swaps 0. Separate
4G/6G/zero-swap scope, TasksMax=128. The legacy negative label continues to
refer to that current-profile mutation, not a historical-profile fixture.

No Lean source changed. The retained CompactTransport/WeightedGroups and
baseline algebra are reused within their existing boundaries; no unchanged
manifest was replayed or new axioms audit claimed. Finite controls and the
host allocation-denial run are not a proof of Rust/LLVM/SBF semantics.

## SBF result and retained regression

R34 compiler exit 0 was rejected by the frame gate (runner exit 1): the
terminal frame was 4480 bytes, 384 over the maximum. Wall 52.80 s, RSS
619740 KiB, swaps 0; 5G/7G/zero-swap scope, TasksMax=128. No SVM execution
was attempted with that ELF. The exact pre-split helper is retained as
evidence/r17-compact-workspace-r34.rs; the stager's --implementation option
can reproduce it. No cap was raised.

R35 moves factor preparation and the two retained block contractions into
a separate non-inlined prepare_rows function. Arithmetic, association,
buffer ownership and transcript remain unchanged. Focused checks pass:
exit 0, 30.32 s, RSS 536256 KiB, swaps 0. Both actual host paths accept:
exit 0, 11.70 s, RSS 449444 KiB; G-final mutation rejects: exit 0, reported
0.00 s, RSS 3520 KiB; swaps 0, 4G/6G/zero-swap scopes, TasksMax=128.

SBF source/table/frame gates pass: exit 0, 40.29 s, RSS 620072 KiB, swaps 0,
5G/7G/zero-swap scope. ELF SHA256:
2650fca6984498ccb43c502d5e1584dc0b9162ab600c56b7d9950a1e8d870871.
Primary acceptance is restored at **25127686 CU**, but this is **919393 CU
slower than R28** (24208293). The compact ordinary marker interval alone is
1568875 CU. Preparation still costs 19892834 CU. This experiment pays for
dense preparation and then compact evaluation; it is not a winning CU route.

Full honest execution still heap-fails in the second reference pass at
25152348 CU. The corrupt full execution heap-fails at 23019904 CU, not a
completed checked rejection. All four 1.2M/1.4M budget cases exhaust CU.
100M diagnostic budget, 256 KiB heap and both verification passes retained.
Driver exit 0, 0.13 s, RSS 30944 KiB, swaps 0; 3G/4G/zero-swap scope,
TasksMax=64; all accounts unchanged. Exact logs, JSONL and source/control
pins are evidence/r17-workspace-*-r35.*. Driver success is not program success.

The next priority is removing expanded preparation with explicitly versioned
compact transcript binding, not further micro-optimization of this duplicate
work. R28 remains the best measured research-v1 primary endpoint.

## Remaining security and implementation boundary

Source refinement of the ownership accessor, slice/cycle loops, edge iterator
and compact tensor/group geometry remains separate from the retained generic
algebra. G still requires a compact evaluator, and expanded-weight transcript
binding still requires dense preparation. Full-transcript privacy, soundness
preservation, oracle/seed correspondence, adaptive losses, retries, failures
and publication are not discharged by this workspace change.
