# Weighted sparse correction and compact ordinary channel

R30–R33 source base b453b56a plus this changeset. These are research-profile
equivalence/implementation steps toward restoring the old compact evaluator,
not a full privacy or soundness theorem. Production paths remain untouched.

## R30: weighted grouped contraction

The old grouped kernel already decomposes the terminal into a 16-entry local
normal vector, three nonzero local carry positions, and a 16-entry high
basis. stage_r17_weighted_groups.py checks and extracts the retained basis,
local geometry and edge routine against both the baseline and staged source.
It preserves the old local arithmetic; the new outer contraction accepts
arbitrary coefficients instead of only binary mask groups.

Kernel::prefix contracts only the supplied prefix (479 coefficients for the
repair's permutation correction). Kernel::binary_masks uses additions for
the fixed reindexed inactive indicator. Kernel::coordinate retains the pivot.
All 64 output groups remain in the right contraction: truncating outputs to
the supported input groups would incorrectly discard propagated carries.
Work selection depends on public lengths/indices/masks, not coefficient values.
The old allocating edge routine is still reused; allocation-free carry
iteration is a further implementation opportunity, not claimed here.

Focused release controls pass: 3072 coordinate cases (all 1024 at zero, one
and generic challenge schedules), 63 arbitrary-prefix cases including partial
16-entry blocks, and 48 binary-mask controls. All four terminal entries match
the retained actual chord/fold source. The R29 repaired-basis controls pass
with the dense correction oracle replaced: 32 tensor, 32 fused-row and 32
arbitrary-weight cases. Exit 0, wall 28.64 s (28.43 compilation), RSS 536144
KiB, swaps 0; isolated 4G/6G/zero-swap scope, TasksMax=128.
Evidence: r17-weighted-host-r30.log and r17-weighted-pins-r30.json.

WeightedGroups.lean proves contract_expand, zero_row and carry_support over
a commutative ring with arbitrary weights and carry matrix. In particular,
zero input rows may be skipped without assuming corresponding output rows
vanish. The source geometry and finite-index correspondence are NOT premises
silently discharged by this algebra; their universal source refinement is
still open. This leaf complements, rather than replaces, the retained
transport/chord/fold proofs and R29 CompactTransport theorem.

Focused lake env lean compile exit 0, wall 1.50 s, RSS 1694872 KiB, swaps 0;
2G/3G/zero-swap scope, TasksMax=64, -j1 -M2500. Cached Lean 4.32.0 commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35 and mathlib
81a5d257c8e410db227a6665ed08f64fea08e997, retained from the rechecked R29
workspace. Exact target AspisV8R17/WeightedGroups.lean, SHA256
107e3089156b32cf36b30b77dfd6e7b2d191dda3ddb38c3063bd2266352db737.
#print axioms: contract_expand/carry_support use propext, Classical.choice,
Quot.sound; zero_row uses propext and Quot.sound. No new axiom or sorryAx.
The first compile failed because the narrow import did not expose sum_comm
(exit 1, 1.45 s, RSS 1676448 KiB, swaps 0); the Sigma import fixed this.
Both r17-weighted-lean-first-r30.log and r17-weighted-lean-r30.log are retained.
No package-wide or unchanged proof replay was run.

## R31: complete ordinary-channel compact evaluator

Description retains the old two-row representation: one XOR12 fused block
for kappa times point 0 plus kappa cubed times point 2, and the kappa-squared
point-1 row. Two 16-by-64 factorizations provide source coefficient lookup
without expanding all 1024 coefficients. Its terminal reuses the exact old
block_terminal_impl bodies, plus the weighted-prefix correction, fixed
inactive-mask contraction, and pivot term from R29's proved decomposition.
Only two 479-entry temporary vectors are used for the permutation correction;
the local kernel does not construct a full chord vector or perform dense folds.

The fixed source permutation is checked to preserve the first 479-coordinate
set, fix every later index, and keep the inactive pivot at 1023. Controls
compare the new Description against the actual r17_opening_weights source:
32 cases times all 1024 original and all 1024 dual entries, plus all 128
terminal entries after the actual chord/four-fold pipeline. Zero/one/maximal
limb points, zero kappa and degenerate zero chord/challenges are included.
All pass. These finite checks do not constitute universal source extraction.

Release gate exit 0, wall 29.19 s (29.17 compilation), RSS 537172 KiB,
swaps 0; isolated 4G/6G/zero-swap scope, TasksMax=128. Observed aggregate
scope peak at least 882909184 bytes. Evidence:
r17-compact-ordinary-host-r31.log and r17-compact-ordinary-pins-r31.json.
This standalone evaluator ends before image-residual and fresh-query terms;
the G channel is separate, not a row silently folded into this description.
The pre-storage-change helper is retained as
evidence/r17-compact-ordinary-r31.rs; pass it as --implementation to the
ordinary stager to reproduce the R31/R32 version rather than the R33 helper.

## R32: research-verifier integration

stage_r17_compact_verifier.py changes only the isolated primary verifier's
ordinary terminal path. prepare still constructs and absorbs the exact old
expanded weights and claim before tau. The prover retains its weights.
The primary ordinary accumulator is reset to the existing eight-variable
query-only accumulator after the first challenge; all four actual challenges
are retained for the compact terminal. The original image_terminal helper
is added to terminal entry 3. G folding, query powers/scales, claim updates,
transcript chronology, opening checks and the whole dense reference verifier
are unchanged. No high-coefficient check or channel is dropped.

The integrated host gate accepts the retained honest proof through both paths
and rejects its existing G-final mutation. Positive exit 0, wall 38.03 s
(38.00 compilation), RSS 537320 KiB, swaps 0; negative exit 0, reported
0.00 s, RSS 3344 KiB, swaps 0. Scope 4G/6G/zero swap, TasksMax=128.
The legacy-labelled negative is the same current-profile G-final mutation,
not evidence about a historical fixture.

The first SBF preflight stopped on an incorrectly composed callback hash
chain, before compiling: the callback aggregate endpoint already included
earlier transformations. The runner now checks the new callback predecessor
against that exact aggregate endpoint, then checks its new hash. Other
files retain their full transformation chain; no source pin was waived.
Evidence: r17-compact-verifier-pin-first-r32.log.

SBF build/measurement results are recorded in R17_REPAIR_CU.md. Source/frame,
heap and supported-budget gates remain separate from host acceptance.

R32 SBF compilation returned 0 but the accepted-build gate returned 1:
Description::new had an estimated 8832-byte frame, 4736 beyond the 4096-byte
limit. No execution or CU measurement was run for that ELF. Compile wall
40.73 s, RSS 619792 KiB, swaps 0, 5G/7G/zero-swap scope, TasksMax=128.
Logs/pins: r17-compact-verifier-{host,build,pins}-r32.*. This failed artifact
is retained, not presented as a runnable optimization.

## R33: bounded storage replacement

Tensor's 16/64-entry factor tables are now built directly into Vec storage,
with a separate non-inlined constructor to bound stack pressure. The
479-entry permutation delta is formed in place by following each fixed
permutation cycle: retain the old first entry, read each old successor before
overwriting the current slot, and use the saved entry for the closing edge.
This removes the second 479-entry vector. All field formulas are unchanged.
The source permutation's prefix closure and uniqueness are essential; this
storage loop does not claim a universal extracted Rust proof.

The 32 complete source-description comparisons pass again after the storage
change: exit 0, 29.28 s (29.24 compilation), RSS 533388 KiB, swaps 0.
The actual honest proof passes both verifier paths: exit 0, 11.87 s (11.85
compilation), RSS 446204 KiB, swaps 0. The G-final mutation is rejected:
exit 0, reported 0.00 s, RSS 3520 KiB, swaps 0. Separate 4G/6G/zero-swap
scopes, TasksMax=128. The stager checks every inherited control pin through
the explicitly recorded R32 callback changes and wrapper addition; it does
not blindly refresh mismatching pins. A local reconstruction matched the
exact staged source/control metadata sent to the NUC.

R33 passes the SBF source/table/frame gate: exit 0, wall 40.41 s, RSS
618528 KiB, swaps 0; 5G/7G/zero-swap scope, TasksMax=128. ELF SHA256
e90911a84a1a1f08e6f52d379e67520d223af7bd7c50b1b7b9958ddeaaa0160e.
At 100M diagnostic budget and unchanged 256 KiB heap the honest execution
reaches compact-ordinary-start, then exhausts heap inside that evaluation:
23663255 CU total, without a primary acceptance checkpoint. This is NOT an
improved completed verifier cost. The corrupt full run exhausts heap at
23019836 CU, also not a completed checked rejection. All four 1.2M/1.4M
cases still exhaust CU. The accepted best primary remains R28: 24208293 CU.

SVM observation driver exit 0, 0.13 s, RSS 31132 KiB, swaps 0;
3G/4G/zero-swap scope, TasksMax=64. Evidence:
r17-compact-storage-{host,proof,build,svm-run}-r33.log,
r17-compact-storage-svm-r33.jsonl, r17-compact-storage-pins-r33.json,
r17-compact-storage-control-pins-r33.json. Its exit 0 records successful
observation, not successful execution of any of the six SBF cases.

## Remaining boundary

The source loop refinement for weighted low/carry geometry and compact tensor
lookup remains to be composed with the existing generic Lean results. The
immediate resource task is to reuse the ordinary dense-weight allocation,
which is currently discarded after binding, for the compact workspace, and
replace temporary allocating edge iteration with the same bounded schedule.
Do not enlarge the heap, remove the dense reference, or call the R33 failure
a completed optimization. The ownership handoff must preserve the prover
and reference verifier's access to the same weight vector.

The 271-node G functional still needs a compact contraction, retaining its exact
mixing map. Expanded-weight absorption still prevents eliminating dense
preparation: exact streaming or a separately versioned descriptor transcript
with justified source/oracle premises is required. Full-transcript privacy,
soundness preservation, adaptive losses, failures, retries and publication
are not closed by these local algebraic results or execution controls.
