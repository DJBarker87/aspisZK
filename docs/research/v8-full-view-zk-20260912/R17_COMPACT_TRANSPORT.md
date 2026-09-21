# Compact baseline reuse through the repaired basis

R29 source base: 5306811d69191ef4d875700dc95c52ce1b484baa plus this changeset.
This advances the compact-evaluator boundary; it is not a new transcript
profile, integrated verifier optimization, CU measurement or privacy proof.

## Exact decomposition and retained proof reuse

Let `P` be the fixed source permutation, `p` the pivot, `I` the inactive
indicator, and `w` an arbitrary coefficient vector excluding that indicator.
Write `delta[j] = w[P(j)] - w[j]`, `other[j] = 1` exactly when `P(j)` is
inactive and not the pivot, and `pivot[j] = 1` exactly when `P(j) = p`.
The new compiled theorem gives, for every linear map L:

    L(transportDual(w + I))
      = L(w) + L(delta) - w[p] * L(other) + L(pivot).

This is the precise route for reusing the old compact tensor evaluator.
Neither the permutation correction nor the pivot subtraction may be omitted.
No honest-witness, nonzero-coordinate, tensor-rank or mask-resampling premise
is used. The source inactive indicator really collapses to the pivot; the
theorem requires and explicitly records that the pivot is inactive.

CompactTransport.lean constructs dualLinear from the retained R16
transportDual, proves its linearity, inactive_to_pivot, dual_split,
compact_transport and delta_zero_off_support. The final theorem
fused_rows_through_repair applies the existing
AspisV8.FusedRows.fuse_through_linear_transport to the composition with
dualLinear. Its old tensor proof is reused, not rederived or weakened.
The identification of Rust's 1024 array indices with five arity-four digits,
and the source chord/fold composition with L, remain source obligations.

## Focused Lean evidence

Cached Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35;
mathlib 81a5d257c8e410db227a6665ed08f64fea08e997. Both pins rechecked.
Every target used lake env lean -j1 -M2500 with an explicit isolated root
and output, in a separate 2G MemoryHigh / 3G MemoryMax scope,
MemorySwapMax=0, TasksMax=64. No package-wide replay or cold dependency build.
Missing project oleans, not an unchanged regression, required the two R16
prerequisites to be compiled into the isolated root.

| Exact target in staged root | Exit | Wall seconds | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| AspisV8R16/BalancedTransport.lean | 0 | 1.69 | 1574968 | 0 |
| AspisV8R16/TransportDual.lean | 0 | 1.57 | 1683172 | 0 |
| AspisV8Baseline/FusedRows.lean, narrowed imports | 0 | 1.77 | 1864800 | 0 |
| AspisV8R17/CompactTransport.lean | 0 | 1.79 | 1866724 | 0 |

All audited results use only propext, Classical.choice and Quot.sound,
except delta_zero_off_support, which uses propext and Quot.sound. No sorryAx
or new axiom occurs in the final successful audit. Unused-section-variable
warnings remain, without errors. The first local bridge compile failed on
a missing `hp` simplification (exit 1, 1.77 s, RSS 1859324 KiB, swaps 0);
its failed audit is retained, not counted as proof evidence.

The first unchanged FusedRows compile exceeded Lean's memory threshold
while loading its broad Mathlib.Tactic import: exit 134, 4.38 s, RSS
2837160 KiB, swaps 0. It was not rerun unchanged with a larger cap.
stage_r17_compact_lean.py checks the original frozen SHA256
a827b5f0b32e1b893d67615a96672d203bf34a9c0c027345bd698175e2999a38,
then replaces only that import with Mathlib.Tactic.FinCases and
Mathlib.Tactic.Ring in the staged adapter. All declarations and proof bodies
remain byte-identical. The repository baseline and its historical evidence
pin remain unchanged. Local reproduction of every staged proof hash matched
the files actually compiled on the NUC.

Logs: evidence/r17-compact-{balanced,dual,fused,bridge}-r29.log.
Retained failures: r17-compact-fused-import-failure-r29.log and
r17-compact-lean-first-r29.log. Exact source/staging pins:
r17-compact-lean-pins-r29.json.

## Actual-source controls

stage_r17_compact_control.py extracts the old block_terminal and
block_terminal_impl bodies byte-for-byte. The whole R17 staged
structured_weights.rs differs from the old baseline because earlier R16
staging changed its callers; that whole-file equality assertion initially
failed. Inspection showed that these two kernel bodies remain unchanged.
The stager now checks precisely those complete bodies against the baseline,
records both whole-file pins, and never replaces the staged verifier caller.

Optimized r17-compact-transport-check passes:

- All 545 source permutation slots 479..1023 are fixed, and every entry of
  the transported inactive indicator equals the single-pivot vector.
- 32 actual v6_statement_points schedules satisfy the old XOR12 complement
  relation used by FusedRows, including zero, one and maximal-limb points.
- 32 unchanged baseline tensor terminals and 32 fused-row terminals, with
  the explicit correction formula, match the actual repaired basis dual,
  chord transpose and four dual folds at all four terminal entries.
- 32 arbitrary non-tensor weight controls satisfy the same decomposition.

Exit 0, wall 27.99 s (27.95 s compilation), RSS 536376 KiB, swaps 0.
Scope 4G/6G/zero swap, TasksMax=128; observed aggregate peak 885547008 bytes.
Gate is optimized release using the retained host cache. Logs and pins:
r17-compact-host-r29.log, r17-compact-host-pins-r29.json. No source verifier
or fixture changed, so unchanged full-proof/SBF suites were not rerun.

## First remaining implementation/proof boundary

The correction contraction in this host control deliberately remains a dense
oracle. Implement and source-bind a sparse/structured contraction for the
actual delta support (slots below 479) and fixed reindexed inactive mask,
including the pivot term. This must compose with the existing chord/fold
proofs for arbitrary extracted coefficients, not only honest proofs.
The G channel's 271-node Vandermonde functional remains an additional
compact-contraction obligation; it is not a single multilinear row and is
not closed by the tensor controls above. Reuse its existing exact mixing
and source-weight lemmas, without changing the map or dropping a channel.

Finally, R17 still absorbs both expanded vectors before tau. Avoiding that
materialization requires either exact byte-preserving streaming or an
explicitly versioned compact-descriptor profile with justified source/oracle
premises and fresh fixtures. None was silently introduced here. The best
measured primary checkpoint remains R28's 24208293 CU; full-program heap,
supported-budget feasibility, full-transcript privacy, soundness preservation,
shared-oracle, retries and publication remain open.
