# R16 soundness preservation obligations

## Checked reducer primitive operations — 2026-09-21

Base `e40ee66066056ef9564df536f31f2ce955e64fa6` plus this changeset.
Exact target `AspisV8R17/UnsignedReducerOps.lean`, SHA-256
`ebe2dfa469ce28c4918e6a5ce6f8d8664d6fc6a107a51bb31c14cc41f48cdcde`,
compiled on the first attempt. Scope `aspis-r17-reducer-ops-r1` in the retained
host workspace; Lean 4.32.0 `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64. Exit 0, wall 0.70 seconds, peak RSS 1626228 KiB,
swaps 0, no warnings. No unchanged formal target was replayed.

Seven statements were proved:

- `cast_value`: unsigned casting is reduction modulo the destination width.
- `narrow_exact`: U64-to-U32 casting is exact when the value fits in 32 bits.
- `and_value`: machine-word AND has the corresponding Nat bitwise value.
- `shift_success`: a checked right shift succeeds below the source width and
  returns the exact shifted Nat value.
- `sub_success`: checked subtraction succeeds when the second operand is no
  larger, and returns the exact Nat difference.
- `shift_overflow` and `sub_underflow`: the complementary invalid cases return
  integerOverflow rather than silently yielding a word.

`#print axioms`: and_value uses `[propext, Quot.sound]`; all other six use
`[propext]`. No sorryAx or new assumptions. The retained Step.Init import
supports the original cast attribute without importing full Scalar.Core.

The five SOURCE blocks (cast including its attribute, shift, scalar-count
shift adapter, AND, subtraction) match the pinned runtime source bytes.
The updated checker authenticated all seven complete runtime source files,
matched all five blocks and rejected three in-memory mutations (shift boundary,
subtraction operator and source tag), exit 0. New complete source pins:

- Bitwise.lean: `63e4b1d0906c972fb4fef953d8d8a60410dcf5313261d2583b1170b4a1a5ce29`.
- Casts.lean: `fd709a15b1e66431b788bf2838b79ac662d4c2afd38acbcde078b775c8f1e668`.
- Ops/Sub.lean: `bd6716dad017ce0c0e9cf9084f9223eb5407ece920853ae7675cbe2362dd5e37`.

Boundary remains explicit: these are the real scalar operation definitions,
not yet the full generated reducer. First remaining proposition is successful
composition of both checked folds, exact narrowing and the final conditional
subtraction, with output equal to retained RawReducer.rawReduceU64. The earlier
first/second-fold bounds and residue theorem were inspected for reuse, not
replayed or replaced. Full CM31 reconstruction and the complete repaired
protocol privacy/soundness obligations remain open. No production paths or
negative regressions were changed.

## Checked current CM31 cross fragment — 2026-09-21

Base `6c8d69cea99dc0c2ead0e48ecde4e8bd786407b0` plus this changeset.
Exact target: `AspisV8R17/UnsignedCM31Cross.lean`. Final source SHA-256:
`993faf1f0594828d209c094fa67e54d49a886487100b34d1ffe0be8e506b7354`.
Four new statements compiled in the same cached Lean 4.32.0 host workspace:

- `widen_value`: the retained U32-to-U64 conversion preserves the Nat value.
- `crossOperand_success`: for four canonical M31 words, the two checked U64
  additions and checked multiplication succeed, returning `(a+b)*(c+d)`.
- `generatedCrossFragment_eq`: the literal generated cross subexpression,
  retaining its lifts, temporary names and checked operators, equals that
  operational composition for all inputs, without canonicality premises.
- `generatedCrossFragment_success`: the authenticated generated subexpression
  succeeds with that exact value under the four canonicality bounds.

All four final `#print axioms` results are `[propext, Quot.sound]`, with no
sorryAx or new cryptographic assumptions. The product bound uses symbolic
monotonicity on two factors below 2^32; no large recurrence was normalized.

The unsigned runtime checker now authenticates five marked cross-leaf blocks
(two aliases, conversion, and checked operator instances), as well as the
unchanged 12-block predecessor. The additional complete source pin is
CoreConvertNum.lean SHA-256
`d7bbeaa3cc7422dcad0a52ffc1904a2d11751717a7b5d820d645404e0bf81eaa`.
The cross checker rejected three in-memory runtime-block mutations.
The generated-source checker separately authenticates the two original field
type declarations and the contiguous cross fragment against the already pinned
Types.lean/FunsChunk04.lean; it rejected two generated-block mutations.
Both checks exited 0 against the final compiled source hash. These checks
authenticate marked text, not a complete extraction/refinement pipeline.

All builds used `-j1 -M1800` with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=64; no cap changed and no whole-package replay ran.

| Scope (prefix aspis-r17-unsigned-cross-) | Result | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| r1 | Missing widening lemma and product elaboration mismatch | 1 | 0.82 | 1608468 | 0 |
| r2 | Conversion and composed cross proof compiled | 0 | 0.74 | 1612268 | 0 |
| r3 | Fragment bind lemma namespace / return identity errors | 1 | 0.74 | 1615064 | 0 |
| r4 | Remaining definitional operator equality | 1 | 0.74 | 1614412 | 0 |
| r5 | All four statements compiled, no warnings | 0 | 0.77 | 1626060 | 0 |

Failed elaborations printed sorryAx and were rejected, not treated as evidence.
The final equality closes by a small definitional operator-instance reduction,
after the explicit Result right-unit proof; it is not a large concrete reduction.

Boundary: the extracted fragment starts AFTER m0/m1 and stops BEFORE
M31.reduce_u64. Its wrapper returns the cross operand, not a CM31 result.
First remaining source-specific proposition is correctness and successful
checked execution of the current extracted reducer on this bounded U64 input,
then composition with m0/m1 and both reconstructed coordinates. The full
CM31 multiplication/square, R17 caller, joint privacy and soundness obligations
remain open. No production protocol path or negative regression was changed.

## Authenticated unsigned execution slice — 2026-09-21

Base `fc8a65e5b4519d7355d8afc3f13075e05eb3b18a` plus this changeset.
`AspisV8R17/UnsignedCoreSlice.lean` compiled in the pinned host workspace with
Lean 4.32.0, `-j1 -M1800`, MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0,
TasksMax=64. No full package replay, cap increase or production change ran.

The slice imports Aeneas.Std.Primitives, BvEnumToBitVec and Nat notation only.
Twelve marked blocks, including the unsigned type, bit width, bit-vector
representation, checked constructor and add/mul definitions, match their
original runtime source bytes. `check_r17_unsigned_slice.py` first authenticates
the complete original Core.lean, Ops/Add.lean and Ops/Mul.lean against pinned
SHA-256 hashes. It accepted all 12 blocks and rejected three in-memory mutations.
The final slice SHA-256 is
`dcdca5dd207a676a8c2d604e045ddc9f00868f66cc645841442b26bd50e9ce2c`.
The checker authenticates marked source blocks, not surrounding framing or
complete caller refinement. The slice cannot be imported with full Scalar.Core,
because it intentionally retains the same unsigned declaration names.

New kernel-checked statements:

- `tryMk_success`: below the selected word-width bound, checked construction
  returns an ok word whose value is exactly the supplied Nat.
- `add_success` and `mul_success`: U64 checked addition/multiplication return
  the exact sum/product under their explicit no-overflow bounds.
- `tryMk_overflow`: outside the bound, the constructor returns integerOverflow.

All four `#print axioms` results are exactly `[propext]`; there is no sorryAx
or new hiding assumption. These are operational scalar facts, not a proof of
the CM31 caller, field reduction, privacy or soundness of the repaired protocol.

| Exact target | Scope (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| AspisV8R17/UnsignedCoreSlice, three success theorems | unsigned-slice-r1 | 0 | 0.70 | 1626412 | 0 |
| AspisV8R17/UnsignedCoreSlice, plus overflow theorem and source checker | unsigned-slice-r2 | 0 | 0.76 | 1619332 | 0 |

The preceding whole-Core split was NOT accepted. Its original source hash is
`ceba1982545251f02d6e286abf23d01f4d2a691fe6934149f3a42d4a051af81e`;
only task-owned copies were edited. Replacing four scalar_tac proof uses and
the tactic import reached checking, but the helper imports needed for the full
file again exceeded the cap. A module-mode experiment was incompatible with
the existing non-module cache. Exact failed target: `Aeneas/Std/Scalar/Core`.

| Scope (prefix aspis-r17-scalar-split-) | Result | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| r1 | Missing task overlay cache dependency | 1 | 0.21 | 539560 | 0 |
| r2 | Missing notation/irreducible_def imports | 1 | 0.96 | 1663804 | 0 |
| r3 | Missing order/tactic helpers | 1 | 5.19 | 1802584 | 0 |
| r4 | Interpreter memory exception after helper imports | 134 | 2.42 | 1845168 | 0 |
| r5 | Module/non-module import incompatibility | 1 | 0.20 | 502916 | 0 |
| r6 | Interpreter memory exception with narrower integer-order import | 134 | 2.44 | 1844688 | 0 |

No axioms audit was obtained from these failed candidates. The abandoned local
candidate remains under target/r17-runtime-split; it is not release evidence.
The task overlay used read-only symlink references to cached dependencies;
the original shared runtime source still matches its hash. No new Core.olean
was produced. A read-only link to the original Core.olean was restored in the
overlay, and the runner now refuses to write an olean through a symlink.
The final runner does not allow the abandoned full-Core build target.

First remaining operational proposition: compose the authenticated U32-to-U64
conversion and these checked operations to prove the CURRENT CM31 cross
operand returns `(a+b)*(c+d)` for canonical M31 inputs; then connect the current
reducer and coordinate reconstruction. Joint-view coverage, commitments,
shared-oracle chronology, retries/publication and full soundness remain open.

## Import-floor localization — 2026-09-21

Base `6cb30c9f5bd740822a51474644a1a58d260244b1` plus this changeset.
Three distinct import probes ran with unchanged Lean `-j1 -M1800` and unchanged
4G/6G/zero-swap systemd scope limits in the same pinned cached workspace.
Each source was just the listed import, a diagnostic comment and the listed
`#check`; no new theorem or new axiom was introduced.

| Probe import / check | Scope (prefix aspis-r17-) | Exit | Wall s | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| Lean / Nat | lean-import-r1 | 0 | 0.55 | 1546656 | 0 |
| Aeneas.Std.Primitives / Aeneas.Std.Result | primitives-import-r1 | 0 | 0.54 | 1554096 | 0 |
| Aeneas.Tactic.Solver.ScalarTac.ScalarTac / Nat | scalartac-import-r1 | 134 | 1.81 | 2013936 | 0 |

The first two checks printed their expected types. The third failed with the
same interpreter memory exception before `#check`. Axioms audit: not applicable
to these import-only probes, and no protocol theorem was compiled. The retained
ScalarImportProbe now contains the third, narrower failing import.

Inspection of Scalar/Core.lean found a direct dependency on this tactic module,
which in turn imports RingNF, Linarith via ScalarTac.Core, and tactic extension
modules. Scalar/Core itself uses scalar_tac in four proof locations (lines
996, 1001, 1142 and 1146), in addition to registering scalar tactic attributes.
Thus removing the tactic import from a copied runtime is not a one-line valid
fix: its proof uses and attribute providers must be handled and recompiled,
without changing scalar definitions or weakening their statements. The shared
runtime and compiled cache were not modified. No cap was raised.

This localizes an engineering obstacle; it is not a mathematical obstruction
to the repair and not evidence of either privacy or soundness. The operational
CM31 proof remains pending. A safe next route is a task-owned, authenticated
runtime split separating scalar semantics from tactic-heavy proofs, with
focused recompilation and exact definition checks before adapter use.

## Current extraction authentication and import-memory isolation — 2026-09-21

Base `2c7a4a8d8f6f14856f1e1d4078c69a35969e0747` plus this changeset.
No new arithmetic theorem compiled in this checkpoint. The current-source
checked-arithmetic adapter remains an uncompiled local draft, not release evidence.

`CurrentFieldSlice.lean` retains 11 generated declarations and their attributes
byte-for-byte from the cached current caller. The read-only checker authenticates
both complete input files before comparing the declaration inventory and bodies:

- Types.lean: `02c93204cbcaa6f5389fed89b9e67074536c6375f990a4504bba297c7780138b`.
- FunsChunk04.lean: `e79e0726e1a58ebfe3701b83f4339ca52b042e46cae833d573df3190c4bd0c21`.
- Narrow-import slice: `a012e37dfa23b84471e5571c73c7c758f774bb0a03aa06ca25f6f29e5e97667e`.

Checker execution with `--self-test` exited 0: 11 declarations matched;
four in-memory mutations (constant, attribute, missing name, extra declaration)
were rejected. This authenticates a source projection, NOT source refinement,
compiled kernel evidence, or an R17 caller theorem. Imports and namespace framing
are outside the byte comparison. Do not import this slice alongside the complete
caller: it deliberately retains the same declaration names.

All following attempts ran on nuc.local in separate user systemd scopes, with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=64, Lean 4.32.0,
`-j1 -M1800`, and the existing pinned mathlib/Aeneas caches. The task directory
was `/home/dombarker/project-offloads/aspis-r17-extracted-cm31.JXBWPZ`.
Time/RSS/swap are GNU time measurements. Every attempt terminated by signal 6
with wrapper exit 134 (the time footer's exit 0 is not a successful compilation).

| Target / change | Wall seconds | Peak RSS KiB | Swaps | Axioms audit |
| --- | ---: | ---: | ---: | --- |
| ExtractedCM31Operands, full caller import, scope cm31-operands-r1 | 3.36 | 2189380 | 0 | Not reached |
| CurrentFieldSlice, Aeneas.Std import, scope cm31-slice-r2 | 1.76 | 2184892 | 0 | Not reached |
| CurrentFieldSlice, narrowed scalar imports, scope cm31-slice-r3 | 1.74 | 2165128 | 0 | Not reached |
| ScalarImportProbe, only Aeneas.Std.Scalar.Core, scope scalar-import-r1 | 1.89 | 2029900 | 0 | No theorem; check not reached |

The first scope names above have prefix `aspis-r17-`; the last is
`aspis-r17-scalar-import-r1`. Each failed with Lean's interpreter memory
exception, not a cgroup OOM. The minimal probe contains only one import and
`#check UScalar`, isolating the obstruction below our arithmetic proof bodies.
No unchanged failed job was rerun with a larger cap; no whole-package build ran.
The narrowed imports did not solve this cached runtime's import-memory floor.

Next engineering step: inspect/reduce the cached Aeneas scalar import closure
under the resource policy before retrying the adapter. First mathematical
obligation remains successful checked execution of the CURRENT CM31 lazy
cross operand with value `(a+b)*(c+d)`, followed by the actual reducer and
coordinate reconstruction. The retained Nat/ZMod theorem does not itself
establish this operational statement. Full privacy and soundness stay open.

## Arithmetic source reuse audit and current CM31 deltas — 2026-09-21

Base `841909cbf881fb07a636bf267ae61fbcd89b7d55` plus this changeset.
Read-only inspection located the cached V7 Aeneas caller workspace on
nuc.local at project-offloads/aspis-v7-aeneas-source-unblock-20260830,
including staged-current-normalized-statement-owned-twohelpers-r19 and its
CurrentCallerAudit. No extraction, replay, deployment or wallet action ran.
Its input field.rs, its normalized field.rs, the current privacy worktree
and v19 staged field.rs all have SHA-256
`5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8`.
The caller audit prints translated definitions and split-helper equalities;
it does not prove the new R17 mask caller merely by existing.

The tracked component-b-weight-at/arithmetic-lean432 README supersedes the
older V5 formula-seam commentary about a general 4.31/4.32 gap: it reports
a 4.32 replay of the source-authentic arithmetic proofs. HOWEVER its pinned
field source is the older blob `a28ff94de05265102ca819849805a7f73c675800`,
SHA-256 `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`.
Comparing that blob to current field.rs finds relevant body changes in
M31::half (low-31 rotate), CM31::mul (unreduced cross-term sums), and
CM31::square (unreduced real-coordinate factors), plus other helpers.
An unchanged QM31 outer body does not erase changed CM31 dependencies.

Manifest authentication was attempted, not assumed:

- The 42-entry SOURCE_MANIFEST.sha256 itself matches
  `7832fe9d7ed7ce56aedc2c568d40354330790af6197720edb58a2f6b0e438a01`.
- The privacy-worktree copy lacks SumProductsComponentLoop.lean,
  SumProductsFullCorrespondence.lean and SumProductsLoop.lean.
- The main workspace has those three files with their expected manifest
  hashes, but its complete check still fails on HalfProof.lean.
- Both copies' HalfProof.lean hash is
  `7f1ee2400114870347fc3b90eda801fcad63197f14c10f8cab06a4eca0a79d6d`,
  whereas the manifest requires
  `d7c073dd5b1740aad11cf7a949c43399f894f5e11c0ffa3fafd8bcd8b4da9fc0`.

Neither copy is accepted as a fully authenticated release replay. No files
were overwritten, copied into the branch or repinned to hide these failures.
The retained LineNorm.lean separately contains the current rotate-half
mathematics; it was inspected, not recompiled or promoted to an extracted
current-source theorem in this turn.

New RawReducer.lean is a narrow replay of retained proof bodies from
V5M31RawMulReduction.lean (lines 55–232) and the addition proofs in
V5ComponentCQM31RustFormulaSeam.lean (lines 160–193). Only the namespace,
imports and minimal aliases change. The full cached reducer import pulled
in the deployment/sampler aggregate and hit the UNCHANGED -M1800 cap.
The replacement avoids those imports and rechecks the literal bit-fold
reducer, canonicality, residue and canonical multiplication/addition facts.

SourceLazyCM31.lean proves the actual new raw cross and square-real factors
do not overflow u64 (and square subtraction cannot underflow), then reuses
that reducer to establish canonical outputs and exact residues. For the
cross term it proves equality to the older reduce-each-sum implementation
as a canonical WORD, not only a congruence. This supplies the mathematical
current-source delta, not equality of a freshly extracted Rust definition.

First remaining source-specific proposition: connect the current extracted
CM31 optimized bodies to these raw graphs and compose them with the retained
QM31 operation correspondences in an authenticated, compatible extraction
universe; then link the R17 mask caller to its mutation model. Existing
source/proof pin failures remain visible. No global privacy, soundness,
source sampler or full-transcript conclusion follows from this delta.

Focused cached `/Users/dominic/ZK/AspisFormal` commands use `lake env lean
-j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, timed with `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| SourceLazyCM31, full cached reducer import | 134 | 45.04 | 4317741056 | 0 |
| RawReducer, narrowed retained proof replay | 0 | 8.84 | 1630748672 | 0 |
| SourceLazyCM31, explicit ModEq conversion still missing | 1 | 2.30 | 1613250560 | 0 |
| SourceLazyCM31, explicit residue equality | 0 | 3.35 | 1630601216 | 0 |
| Privacy-worktree manifest check | 1 | 0.03 | 7405568 | 0 |
| Main-workspace manifest check | 1 | 0.01 | 7045120 | 0 |

The memory failure was an import/dependency problem, not permission to raise
the cap. All nine final axioms audits use only subsets of propext,
Classical.choice and Quot.sound, no sorryAx, and both final leaves have no
warnings. No production source, unrelated work, negative regression or pin
was changed. No full manifest compilation or unchanged runtime suite ran.

## Reverse table writes and noninterference — 2026-09-21

Base `2c038f925ba5500abc4aa1362dc07f5dca5d51fb` plus this changeset.
`ConsecutiveWrites.lean` proves sequential Function.update writes preserve
every outside entry, write the intended inside entry, compose by list append,
and commute for adjacent disjoint blocks. These facts are symbolic in lengths;
the proof never normalizes a concrete 271-write chain.

`MaskWeightWrites.lean` models the source's actual high-round-to-low-round
chronology, writing each literal inner power-loop block and then writing
the final carry scale at zero. The table equals writing the proved flat mask
weights, entry by entry, for ANY initial table. Thus initialization values
cannot leak into an unfilled coordinate in this model. The model leaves
entries above 270 unchanged. A separate arithmetic lemma proves that every
1+27*r+i address (r<10, i<27) is nonzero and below 271; another proves those
addresses are injective. The final source_written_mask_pairing consumes this
mutating-table model in the already-proved mixing/mask functional identity.

The previous recursive-block-to-mutation-model gap is now discharged.
This remains a mathematical mutation model, not an imported Charon/Aeneas
translation of the pinned Rust function. No equality between extracted
Rust code and this model is silently assumed or claimed proved.

Read the retained V5ComponentCQM31RustFormulaSeam.lean and
V5M31RawMulReduction.lean before considering field instantiation. The former
explicitly states that executable-function equalities remain named premises
(including RustCanonicalM31PrimitivesMatch), and documents a historical
cross-toolchain raw-add seam. The latter proves the mathematical literal
two-fold M31 reduction graph and canonical bounds. Their existence alone
does not close the present Rust execution/field boundary. Existing exact
tower and raw-operation work should be reused, not replaced with a new
field assumption or another cold dependency replay.

First remaining source-specific proposition: an exact pinned Rust execution
refinement, or a composed source-locked semantics proof, connects mask_weights
array mutation, its caller's point-array conversion and QM31 operations to
sourceMaskTable and the exact tower. Point-construction, concrete order,
commitment/image/fold/extraction and adaptive-challenge gates remain open.
Joint privacy coverage and full-transcript simulation are not implied by
this opening-functional result.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`, per-leaf command
`lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ConsecutiveWrites | 0 | 7.51 | 1214808064 | 0 |
| MaskWeightWrites, dependent bridge | 0 | 8.98 | 1804025856 | 0 |

All twelve #print axioms outputs use only subsets of propext,
Classical.choice and Quot.sound, with no sorryAx. ConsecutiveWrites emits one
unused simp-argument warning; MaskWeightWrites has no warnings. No production
path, source pin or negative regression changed. No full manifest, cold
dependency build, Aeneas replay or unchanged runtime suite was launched.

## Structured-mask weights, carry and source slices — 2026-09-21

Base `42596fba8798302aaf5290d28a0303b9a7f27611` plus this changeset.
Three new leaves discharge the earlier flat-coordinate algebraic gap:

- `MaskWeightBlocks.lean` proves the scaled 27-entry round-block dot
  product, matching list lengths, reverse-round block construction and
  carry scale half^r. The complete carry-plus-block dot product equals the
  literal mask loop and, at half=1/2, the retained structuredMask.
- `MaskWeightVector.lean` proves the literal inner power-weight recurrence
  and supplies a length-checked Fin 271 interface for the ten 27-entry
  blocks plus carry. No truncated zip or omitted coordinate enters it.
- `MaskSourceSlices.lean` proves that reads starting at 1 and advancing
  by 27 flatten to exactly the original 271 coordinates including carry
  at zero. The final source_mask_weights_pairing discharges the intermediate
  slices equality premise for the SAME computed Horner outputs. Its final
  source_original_mask_weight_dot composes the mask evaluation with G's
  retained point-1, point-2 and inactive-sum terms.

The final pairing is not conditional on a new hiding/coverage premise.
It is deterministic source-shaped algebra for arbitrary m and challenge
coordinates. In particular, no source coin is resampled and the 271 mixed
coordinates are not asserted independent or uniform. The intermediate
mixed_mask_weights_pairing still documents its slices premise; the final
MaskSourceSlices theorem actually proves and instantiates that premise.

Rechecked local and v19 staged r17_structured_g.rs, identical SHA-256
`147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.
The inner power recurrence, source slice offsets, reverse chronology and
carry contribution are now represented and proved. The outer weight-table
construction is a recursive block model: equality to every Rust mutable
array write has NOT been claimed as an extracted execution theorem.

First remaining source-specific proposition: the pinned Rust mask_weights
array writes, field operations and point-array conversion refine these
flat blocks and the composed opening functional. The point-construction
API, concrete field representation, fixed inventory/order and full verifier
acceptance/extraction still need their source connections. This does not
discharge commitment binding, high-tail image validity, folds/final openings,
adaptive challenge losses, joint legal C1/H1/G coverage or full privacy.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; per leaf command
`lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| MaskWeightBlocks | 0 | 10.49 | 1705148416 | 0 |
| MaskWeightVector | 0 | 8.77 | 1795915776 | 0 |
| MaskSourceSlices, initial distribution/rewrite failure | 1 | 6.42 | 1790836736 | 0 |
| MaskSourceSlices, side-restricted rewrite; congr recursion failure | 1 | 5.88 | 1773158400 | 0 |
| MaskSourceSlices, explicit function equality | 0 | 3.93 | 1801912320 | 0 |
| MaskSourceSlices, added original-weight composition | 0 | 1.94 | 1802960896 | 0 |

Seventeen final #print axioms declarations contain only subsets of propext,
Classical.choice and Quot.sound; no sorryAx. Final leaves have respectively
one, two, and three unused-instance/simp-argument warnings. The failed
drafts were not evidence. Their replacement uses symbolic distributivity,
restricted rewriting and function extensionality, not increased limits or
normalization of the 270-entry list. No production changes, removed negative
regressions, full manifest replay or unchanged runtime replay occurred.

## Original opening weights and mixing transpose — 2026-09-21

Base `8a58262abc8429cefe370cccbc9e4f1f9e0f2a97` plus this changeset.
`SourceOriginalWeights.lean` models the length-10 multilinear component's
multiply-accumulator, with the exact big-endian bit-position expression
`(index >> (9-coordinate)) & 1`. It proves the product form, then models the
original_weights component list, inactive-row addition, and optional G term.
The ordinary branch has all three point components with scales kappa,
kappa^2, kappa^3. The structured branch replaces ONLY the first component
with kappa times the supplied G-weight vector. The other two point components
and inactive-sum claim remain. A composed theorem feeds this exact model into
the retained transport/chord/residual opening identity for arbitrary q.

The three length-10 point arrays are explicit inputs. The point functional
is explicitly the dot product against the big-endian basis; this is not yet
a refinement of every existing EvaluationClaim or point-construction API.
The source v6_statement_points constructs z, a carry-propagated successor,
and the point with coordinates 7 and 6 flipped; the model does not silently
substitute independent points or assume those constructions have been proved.

`SourceMixingWeights.lean` proves the power-row generation recurrence, the
nested weighted-row accumulation formula, and its dot-product identity with
the SAME 271 reverse-Horner outputs of the original 1024-entry vector.
Its final theorem instantiates the structured original-weight functional
with this mixing transpose, retaining the other two point functionals and
the inactive sum. No fresh mask, uniform prefix law or new hiding assumption
is introduced. The 271 coin weights remain explicit inputs.

First remaining source-specific proposition: the actual reverse-round loop
that writes coin_weights[0] and the ten 27-entry slices at 1+27*r produces
the linear functional for the retained mask_eval, including the carry scale,
zero-boundary coefficients, and complete round chronology. Then connect the
point construction and Rust array/field operations to the model, rather than
treating this source-shaped algebra as execution extraction. Source joint
coverage, commitment extraction, image/fold/final consistency, shared-oracle
challenge bounds and full privacy/soundness losses remain separate open gates.

Inspected source pins (local and v19 staged core files identical):

- sumcheck.rs, add_multilinear and weight_at:
  `7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead`.
- v6_transcript.rs, v6_statement_points:
  `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf`.
- r17_structured_g.rs, mixing_row/mixed_coins/mask_weights:
  `147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.

The two modules were compiled smallest-first in cached
`/Users/dominic/ZK/AspisFormal`, using `lake env lean -j1 -M1800 -R
<research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured by `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| SourceOriginalWeights | 0 | 8.14 | 1480966144 | 0 |
| SourceMixingWeights, broad simp/CharP recursion failure | 1 | 12.08 | 1767047168 | 0 |
| SourceMixingWeights, restricted simp; remaining composition | 1 | 7.03 | 1781071872 | 0 |
| SourceMixingWeights, explicit Function.comp_def and integrated bridge | 0 | 2.16 | 1803141120 | 0 |

The fix was explicit symbolic rewriting, not a recursion/memory-cap increase.
All ten final #print axioms outputs contain only subsets of propext,
Classical.choice and Quot.sound, with no sorryAx. Both final leaves have no
warnings. Failed drafts were not accepted as evidence. No production paths,
negative regressions, full manifests or unchanged runtime suites were changed
or replayed.

## Composed source-shaped opening identity — 2026-09-21

Base `aba46950365f4b90214027d1e1441355b0a61b3f` plus this changeset.
Four focused leaves now connect the previously separate algebraic steps:

- `ChordDual.lean`: finite dot-product padding lemmas and the full-width
  even/odd chord pairing. All 514 positions per output lane remain present.
  The single-scatter extra coordinate is eliminated by its proved support
  bound, while the double scatter retains the complete intermediate vector.
- `SourceChordTranspose.lean`: parity-sum/interleaving identities and the
  source-shaped 1024-coordinate chord transpose, with both weight lanes
  zero-extended from 512 to 514. Its pairing holds for arbitrary q.
- `SourceOpeningResidual.lean`: literal sequential updates at 1023, 1022,
  1021, then the separate ordinary and structured-G channel pairing.
- `TransportedOpening.lean`: composes the result with TransportDual's
  arbitrary-coefficient identity, converting between finite row indices and
  the natural-indexed source-loop model.

The final theorem `transported_source_opening_pairing` states that the
computed quotient-weight dot product is the original-weight dot product on
inverseTransport(sourceChord(q)), PLUS the actual channel residual terms.
There is no honest-generation, legal-mask or residual-zero premise on q.
The theorem parameterizes the public order and inactive set; exact source
inventory correspondence remains required.

The compiled two-channel formula retains precisely:

```
tau   * qR[1023]
+ tau^2 * (b*qR[1022] - c*qR[1021])
+ tau^3 * qG[1023]
+ tau^4 * (b*qG[1022] - c*qG[1021]).
```

These are not silently set to zero. The combined image check still needs
the ordinary/carried-error term and its degree-4 accounting from the retained
two-channel argument. The pairing is deterministic algebra, not a root-count
or Fiat--Shamir distribution theorem.

Crucially, weight zero-padding proves a pairing with the retained low 1024
forward coefficients even if the four high output coefficients are nonzero.
This does not prove high-tail-zero acceptance or that a malicious quotient
lies in the required image. The audit's high-tail assertion is not inherited
as an assumption. That distinction preserves the separate image soundness gate.

Rechecked local r16_basis_transport.rs SHA-256
`36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`;
local and v19 staged r17_opening_weights.rs are identical at SHA-256
`bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
This is a mathematical model of that source shape, not an extracted Rust
execution proof. Original weights, the source field embedding/word operations,
array reads/writes and the concrete fixed inventory remain source obligations.

First remaining source-specific proposition: `original_weights` and its
WeightAccumulator/structured-mask materialization, together with the actual
field/array implementation of the composed pipeline, realize this identity
for both channels and arbitrary extracted coefficients. Commitment extraction,
image validity, all folds/final openings, adaptive challenges and explicit
soundness loss still require their own proofs. The joint legal C1/H1/G
coverage and full-transcript privacy gates are unchanged, not discharged.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; each leaf compiled
with `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, measured with `/usr/bin/time -l`:

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ChordDual, initial partial-application simplification | 1 | 8.55 | 1427341312 | 0 |
| ChordDual, explicit unfolding of partial applications | 0 | 1.90 | 1445609472 | 0 |
| SourceChordTranspose | 0 | 1.81 | 1444331520 | 0 |
| SourceOpeningResidual | 0 | 2.99 | 1444249600 | 0 |
| TransportedOpening, dependent composed bridge | 0 | 2.61 | 1468203008 | 0 |

Twelve final #print axioms declarations use only subsets of propext,
Classical.choice and Quot.sound. No sorryAx. SourceChordTranspose emits two
unused section-instance warnings, SourceOpeningResidual one unused simp
argument warning; the final bridge has no warnings. The failed initial draft
was not proof evidence. No cap increase, production change, full manifest
replay, or unchanged runtime regression occurred.

## Bounded source scatter/gather adjoint — 2026-09-21

Base `3a53c79a5003755c885fd6b87e98b9d046a9d51d` plus this changeset.
`AspisV8R17/ScatterDual.lean` proves the finite dot-product identity for
the retained scatter edge lists and their gather operation. Input and output
index bounds are explicit. It identifies the gather of sourceEdges with
the weightedIndexLoop read sum, and instantiates the adjoint at any retained
bounded schedule. This uses the existing index certificate, not another
enumeration of dense field matrices.

`AspisV8R17/SourceGatherLoop.lean` models the accumulator in the verifier's
xt: on each set bit it clears the bit, multiplies scale by half, and adds
the weighted read; the final read sets the first clear bit. It proves this
loop equals the weighted read sum. The retained certificates discharge
termination at all inputs below 512 and 513. The double-scatter adjoint
preserves the actual 512 -> 513 -> 514 forward sizes and reverses them for
the gather; the 513 intermediate coordinates are not discarded.

Inspected local tools and identical v19 staged files:

- r17_opening_weights.rs SHA-256
  `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
- r17_coupled_audit.rs SHA-256
  `74f6ec7eff5c747656168dabd1cefd9cb7326fc29c9fd6ccf2d46a10e944c690`.

The opening code pads weights from 1024 to 1028, splits even/odd lanes,
gathers to 513 and then 512, and recombines 1024 weights. The audit's forward
chord computes 1028 coefficients, asserts its high tail zero, then truncates.
The new identities hold for arbitrary inputs at the stated dimensions;
they do NOT assume or establish that high-tail assertion. In particular,
an honest diagnostic assertion is not a malicious-prover image proof.

Next exact proposition: combine these adjoints with the retained
finiteChordEven/finiteChordOdd equations, preserving parity splitting and
zero-extended weights, to prove the entire chord_transpose pairing. Then
compose with TransportDual and the two distinct residual-weight formulas.
Word-level Rust/field refinement, original-weight materialization, extraction,
challenge bounds and the joint privacy obligations remain open. No new hiding
or adjoint assumption was introduced.

Focused cached workspace `/Users/dominic/ZK/AspisFormal`; command for each
leaf: `lake env lean -j1 -M1800 -R <research>/lean -o <r17-cache>/<leaf>.olean
<research>/lean/AspisV8R17/<leaf>.lean`, timed by `/usr/bin/time -l`.

| Target/attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| ScatterDual, initial map-composition simplification | 1 | 10.18 | 1430159360 | 0 |
| ScatterDual, explicit Function.comp_def | 0 | 4.62 | 1444233216 | 0 |
| SourceGatherLoop, loop identities | 0 | 1.72 | 1445806080 | 0 |
| SourceGatherLoop, added double-scatter bridge | 0 | 3.32 | 1447788544 | 0 |

Three ScatterDual and five final SourceGatherLoop #print axioms results use
only subsets of propext, Classical.choice, Quot.sound, with no sorryAx.
The failed draft was not accepted evidence. No production changes, cap
increases, full-manifest replay or unchanged runtime suites were performed.

## Universal inverse-dual algebra — 2026-09-21

Base `7048dd6bb844a46ba49d5f224800720e915da3be` plus this changeset.
New `lean/AspisV8R16/TransportDual.lean` proves `inverseTransport_dot`:
for EVERY coefficient vector c and weight vector w over a commutative ring,
the dot product of w with inverseTransport(c) equals the dot product of the
explicit transported weights with c. There is no honest-generation,
balanced-mask, or legal-witness premise. The forward corollary uses the
retained inverse theorem and pivot membership. This closes the universal
model-level algebraic identity, not its exact-source refinement.

The weight formula subtracts w(pivot) exactly at rows in inactive.erase(pivot),
then permutes by order. This is the predicate `r != PIVOT && inactive[r]`
in the inspected Rust `Transport::dual`. The generic permutation model still
requires source inventory correspondence; the Rust forward/inverse loops
specifically rely on their constructor leaving PIVOT in the final slot.

Inspected identical local tool and v19 staged `r16_basis_transport.rs`:
SHA-256 `36466ca34b091ee2e058deb3c66d1306164c0b6869719586175ddefa87a37dcf`.
Inspected staged `r17_opening_weights.rs`:
SHA-256 `bc0068b47eba5f871fac7ff809aad79bff738357ead553fa2ded7fd579428fec`.
Its quotient_weights applies this dual to original_weights, then the chord
transpose, then the separate ordinary/structured image residual weights.
The new theorem does NOT prove that chord transpose, original-weight
materialization, residual checks, Rust field operations or extraction.

Focused cached compilation in `/Users/dominic/ZK/AspisFormal`, using
`lake env lean -j1 -M1800 -R <research>/lean -o <r16-cache>/TransportDual.olean
<research>/lean/AspisV8R16/TransportDual.lean`, measured with `/usr/bin/time -l`:

| Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial sum rewrite | 1 | 8.70 | 1424359424 | 0 |
| Pointwise rewrite; remaining finite-set equality | 1 | 5.18 | 1423835136 | 0 |
| Explicit finite-set extensionality | 0 | 3.19 | 1437286400 | 0 |

Both final #print axioms results contain only propext, Classical.choice,
Quot.sound; no sorryAx. Failed attempts were not accepted proof evidence.
No resource cap increase, production change, unchanged runtime regression,
or full-manifest replay was performed.

First remaining soundness-specific proposition: the exact staged opening
weight pipeline, including chord transpose and distinct channel residuals,
computes the required functional on arbitrary extracted coefficient vectors.
Its Rust/field refinement and subsequent binding, extraction, adaptive
challenge and loss-accounting gates remain open. Joint legal C1/H1/G privacy
coverage remains a separate obligation; this soundness lemma does not close it.

Date: 2026-09-20. Base privacy revision `1d77761f`.

The raw C1 privacy separator is not evidence of a soundness break. However,
R16 changes the encoding/verification relation and must not inherit a
soundness verdict solely because honest fixtures pass.

## What follows from the reversible map

At the algebraic model level, `transportEquiv` supplies both inverses of T.
For any encoder E on the complete message space, `range(E ∘ T) = range(E)`:
one inclusion applies E to Tm, the other chooses `T⁻¹m`. Thus this basis
change does not itself enlarge the ambient codebook or change the set of
codewords on which distance/list bounds are stated. This is a mathematical
consequence, not a compiled end-to-end soundness theorem or a statement
that all such messages satisfy the payment relation.

Original semantic messages and constraints must continue to refer to
`m = T⁻¹c`, where c is the extracted encoded coefficient vector. The
required functional identity is `dot(w,m) = dot(T⁻ᵀw,c)`. It must hold for
arbitrary maliciously supplied c, not merely honestly produced witnesses.
M31/QM31 basis tests and the staged dense differential checks exercise this
identity; its exact-source universal formal refinement remains open.

## Required source gates, none waived

| Gate | Checked evidence | Remaining proposition |
| --- | --- | --- |
| Fixed public transform | Source-derived immutable order; legal-cell assertions; inverse tests; generic Lean equivalence | Concrete Rust loops/field operations refine that equivalence |
| Joint commitment extraction | Both C1 and C2 use the same T; ordinary encoder and Merkle verification retained | Binding/extraction for the new profile yields a coherent c for every batched column |
| Original semantic relation | Ten-round semantic code remains on original rows; honest public-byte verification passes | Accepted point claims equal evaluations of T⁻¹c except for an explicitly bounded bad event |
| Functional transport | Inverse dual precedes chord transpose; dense and entrywise calculations agree in controls | Universal exact-source dual/chord identity and batching bounds |
| Quotient/image condition | Existing top-coefficient checks and verifier image terminal retained | Extracted quotient satisfying new functional checks corresponds to the same encoded polynomial, including all exceptional OOD cases |
| Final values/openings | Existing authenticated openings and structured/dense outcome comparison retained | Full extraction and consistency theorem through all folds and Final256 |
| Fiat–Shamir chronology | Distinct R16 profile absorbed by prover and verifier; exact map included in descriptor | Source oracle transcript, challenge distribution, query budget and soundness loss for this profile |
| Invalid proofs | Both exercised witnesses accept; byte-corruption/truncation controls reject | Quantified malicious-prover soundness, not a finite mutation sample |

The first soundness-specific source theorem is the universal transported
functional identity for the exact verifier weights, composed with the
existing chord transpose and original point/inactive claims. The wider
commitment/extraction and Fiat–Shamir obligations still need their own
premises and loss accounting. The new profile changes transcript bytes;
old challenges or old proof bytes cannot be assumed identical.

There is no current full soundness-preservation claim, no full privacy
claim, and no release/deployment approval. Closing either ledger alone is
insufficient for the user's full-repair goal.

## R17 structured-G integration boundary (2026-09-20)

The R17 prototype would require a G-specific opening functional. The R16
source instead proves one functional of a single gamma-batched message.
`R17_MIXED_MASK_BOUNDARY.md` records source hashes, a compiled impossibility
lemma for unequal functionals on a single combined input, and an executable
negative regression. Changing a common inverse-dual weight cannot repair
that mismatch. A distinct opening argument (such as the specified, still
unimplemented two-channel route) must be soundness-checked; the old verifier
must not be patched to accept unmatched claims. This is not a demonstrated
soundness break in the unchanged protocol.

The next R17 step is now an arithmetic prototype, documented in
`R17_TWO_CHANNEL_OPENING.md`. Its two functionals remain distinct through
both quotient channels, four image residuals and four relation rounds.
The compiled root-count bounds must include the ordinary/carried error:
degree 4 for the combined image check and degree 44 for the combined
query check. The smaller image-only degree-3 bound is not the whole gate's
soundness bound. Uniform challenge, source chronology, binding/extraction
and adversarial query-budget premises remain open; no end-to-end loss or
soundness-preservation claim follows from the prototype.

The subsequent `R17_SOURCE_INTEGRATION.md` records a matched staged host
implementation and honest/negative runtime controls. This advances source
implementation, not the universal extraction/refinement or Fiat--Shamir
soundness gates above. Production protocol paths remain unchanged.
