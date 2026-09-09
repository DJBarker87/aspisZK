# Inverse-cell masking adapter: deterministic preservation

Source pin `33e13de4e4b8bfdef7f3f2fb2e472b34db44865e` on the research branch.
This subtask adds only a focused mathematical leaf, runner and this report;
the parent agent owns the separate isolated Rust integration. Production,
the selected V7 sources, main and deployment remain unchanged.

## Exact operation being modeled

The research adapter retains the legacy mask generator's entire sequence of
draws and the existing `apply_pool_v1_pair_forest_mask_material_v1` call. It
then overwrites `(row1014,column3)` with the inverse witness **before C1 is
committed**. The random draw previously used at that cell is discarded, not
transferred to a different cell or counted as a new mask. A distinct research
profile binds the changed semantics; old fingerprints in the legacy entropy
API still identify that generator accurately.

This is not the different implementation that shortens the old draw sequence
to 3,802 values. Shortening it would shift all subsequent mask-only/G/H draws.
No privacy equivalence between either implementation and the old protocol is
inferred from the layout result.

`apply_mask_material_for_layout` is **not** just pointwise random additions.
It chooses the last allowed inactive cell in every semantic column, adds the
3,803 supplied masks, then overwrites each chosen dependent cell with minus
the sum of the other inactive entries. The proof therefore includes these
balancing writes, rather than assuming they preserve the inverse cell.

## Source map and obligations

| Pinned source | Required fact |
|---|---|
| `pair_forest_hiding.rs:212–258` and `pair_tree_hiding.rs:300–334` | `(1014,3)` is in the old mask inventory; neither local amount factor `(1014,1)` nor `(1015,1)` is |
| `pair_trace.rs:1103–1132`; forest registry translation | Existing Copy edges use only the amount/partial cells at these conservation rows, not column3; row1014 is already Copy-active |
| `aspis-prover/state_only_hiding.rs:421–470` | Legacy material generation/order; one old random draw is later overwritten, not removed from this stream |
| `state_only_hiding.rs:668–710` | Material shape/length check, per-column dependent selection from the allowed list, all random additions, then inactive balancing |
| `state_only_hiding.rs:169–181` | A dependent cell receives minus the sum of all other inactive entries; active dependents reject |
| `state_only_hiding.rs:611–633,754–768` | Existing context fingerprints and legacy mask list remain the generator/application identities |
| `PaymentMaskRead.lean` | Existing decoder-field footprint disjointness; reused unchanged |
| `SelectedTransferPositive.lean` | New product residual's amount-binding consequence; reused unchanged |

The concrete integration must test the generated active-row table and actual
dependent selection, not choose convenient substitutes: row1014 active, each
selected dependent a valid allowed inactive cell, and (for this layout) last
dependent row1023 in every one of the sixteen semantic columns. These facts
instantiate explicit parameters of the new theorem. They are not supplied
as universal facts about arbitrary mask schedules. The parent's isolated
`positive_transfer::layout_control` now tests those concrete facts. Its
[honest-run evidence](evidence/positive-transfer-honest-v1.log) records the
old/new mask fingerprints `f9daf3d54f4285d1` / `6b661245a56c7189`, unchanged
sixteen dependents, active reserved row and 107 verifier-derived profile
bytes. These are differential/source execution checks, not a Lean translation
of the Rust registry.

The source `recovered_witness::decode` additionally scans **all** raw C1
limbs for canonicality and checks shape. `PaymentMaskRead.readCell` denotes
the narrower witness-field footprint. Preservation of that footprint does
not license noncanonical raw encodings elsewhere; actual M31 additions,
balancing and inverse writes must preserve canonicality separately.

## New mathematical interface

[SelectedTransferMaskAdapter.lean](experiments/SelectedTransferMaskAdapter.lean)
models an arbitrary table and arbitrary field-mask deltas. Its balancing map
is the literal finite-sum/one-dependent-per-column algebra of the source.
No honestly generated trace, decoder success or valid-witness premise is used.

| Interface | Precise role |
|---|---|
| `reserved_was_mask` | Derives membership of `(1014,3)` from the existing source-shaped mask predicate |
| `DependentMaskSupport` | Names the source fact that each chosen dependent belongs to the original allowed mask set |
| `balance_protected` | Balancing writes cannot alter a cell outside that mask set |
| `balanced_inactive_sum_zero` | Derives the zero inactive sum from the actual negative-sum assignment, finite-row membership and inactive-dependent hypotheses |
| `overwrite_preserves_inactive_sum` | Writing any value to active row1014 leaves every inactive-column sum unchanged |
| `adapter_protected`, `adapter_decoder_reads` | Legacy additions, dependent balancing, then restoration leave every original protected cell / decoded witness field unchanged |
| `adapter_inactive_sum_zero` | Composes the actual balancing formula with the active overwrite; no assumed preexisting zero sum |
| `adapter_product_residual` | The repaired table's three-cell product equation is exactly `original_r * original_c * supplied_u - 1 = 0` |
| `original_mask_writes_reserved` | Explicit regression: the original pointwise masker does modify the new inverse cell; the restoration is necessary |

The row set is symbolic and finite; the proof does not normalize a 1,024-row
or concrete-field enumeration. Instantiation with `Finset.range 1024` is an
interface choice, not another sum expansion.

## Formal status and evidence

**Kernel checked.** The existing `PaymentMaskRead` replay produced no
`.olean`; exporting that unchanged pinned leaf was necessary to import it.
Its source was not modified. All new audited results use only
`propext`, `Classical.choice` and `Quot.sound` (some use a subset).
No new axiom or `sorry` occurs in the retained proof.

| Exact focused target | Exit | Wall time | Peak RSS | Swap | Evidence |
|---|---:|---:|---:|---:|---|
| Missing `PaymentMaskRead.olean` export | 0 | 6.11 s | 2,881,060,864 B | 0 | [export log](experiments/selected-transfer-mask-export-v1.log) |
| Adapter v1, two local proof errors | 1 | 15.91 s | 5,488,017,408 B | 0 | [failed log](experiments/selected-transfer-mask-adapter-v1.log) |
| Changed adapter v2 and nine axiom audits | 0 | 4.27 s | 5,629,870,080 B | 0 | [successful log](experiments/selected-transfer-mask-adapter-v2.log) |

The initial errors were three tiny source XOR constants left unevaluated by
`norm_num` and generic subtraction not definitionally equal to addition of
negation. The replacement uses decisions only on those three small XOR
equalities and `sub_eq_add_neg`. There was no memory-pressure failure or
larger-cap retry. The v1 error log's `sorryAx` is Lean's unsuccessful-error
recovery output, not retained evidence; the complete v2 audit has none.

The runner pins the inherited source/olean chain, mathlib and Lean 4.32.0,
uses the existing cache with a serialized 7-GiB process-tree RSS guard and
`lean -M7000`, and records the full commands. No cold dependency or
package-wide Lean/Aeneas replay ran. New source SHA-256:
`4df18612b7c635c34fa0c1e9949c8f1b81b857f5bd1e2a1ec0ded57039395b5a`;
exported olean:
`8bf8365c7fa3d3760157a8ecd7dd8632a936a6f58354d0de26560e377ee48374`.

From the research worktree, use a fresh log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_transfer_mask_adapter.sh leaf docs/research/v8-no-work-100-20260907/experiments/selected-transfer-mask-adapter-recheck.log
```

On a cache without `PaymentMaskRead.olean`, first use the runner's
`export-mask` mode and a fresh log. The existing export is deliberately not
rerun unchanged once present.

## Precise next privacy gate: remove a column, then model the new view

The reusable old full-view matrix is in
`crates/aspis-prover/src/state_only_hiding_rank.rs`, not in this new Lean
layout proof. Its `probe_pool_v1_pair_forest_root_message_hiding_rank`
function (lines 4641–4658) **requires q16** and selects
`FactorSchedule::Production`, `PcsSchedule::RootMessageV6Log20` and
`RankLayout::PoolPairForestV1`. The selected test is
`pool_pair_forest_exact_layout_spans_complete_root_message_view` in
`tests/pool_pair_hiding_rank.rs:108–142`.

The latest located exact forest measurement is the fixed-schedule NUC result
recorded in [the eight-lane gate](../v7-pool-eight-lane-concurrency-gate-20260827.md):
sumcheck rank 1080/1084, joint PCS rank 4092/4360, physical/legal/helper
containment `Some(true)`, 1,187.279 seconds test time, 1.2 GiB cgroup peak,
zero swap. It uses the **old 3,803-cell registry and q16 V6 root-message
sequence**, not the V8 q22 component-OOD/chord/image/shifted-row transcript.
Those figures are inherited evidence, not new measurements in this task.

The exact reusable matrix construction is at
`state_only_hiding_rank.rs:5494–5565`:

1. Group the old allowed cells by semantic column and select each last
   inactive dependent.
2. For every nondependent cell form its raw-opening vector with
   `c1_raw_difference`, and carry its masked-sumcheck/PCS vector with
   `scaled_aux_difference` through `CarryEchelon`.
3. An inactive cell subtracts its dependent generator. The reserved
   **active** `(1014,3)` has `subtract=None`; removing its random influence
   therefore deletes that exact generator, without changing any dependent.

Thus the first controlled delta is concrete: reconstruct the same fixed
matrix, omit **only** `(column3,row1014)` from its semantic mask basis, and
check whether its former raw-plus-sumcheck-plus-PCS image is in the span of
the remaining columns. Do not just decrement a published rank or delete a
pivot by declaration. The report type already exposes
`raw_opening_minor`, `masked_sumcheck_minor`, `joint_raw_sumcheck_minor` and
`post_sumcheck_pcs_minor`. `RankMinorProvenance` (line 624) stores source
column IDs, pivot rows, M31 pivot values and a fingerprint. The generator's
stable source ID must be captured at the enumeration above. If that ID is
in a chosen minor, explicitly replace the pivot or exhibit a dependence.
The current test prints counts/containment booleans rather than those pivot
vectors; no serialized forest pivot matrix was located in the bounded
research-artifact search. Consequently this is not presented as an
already cached, trivial-duration rank update. Rebuilding its elimination
belongs on the bounded optimized build host, not an uncapped local replay.

That old-view column test is only a **falsification/control gate**. Passing
it would not settle V8 privacy. The actual next full-view model must include
q22 complete raw openings, **both separate component-OOD vectors in their
real order**, the corrected semantic responses (including the new cubic
inverse constraint), final256, shifted ordinary rows, carried image weights,
initial mask claim, and all other public responses from the same transcript.
A batched root-message image must not be assumed to determine separately
disclosed component evaluations. The inverse is a witness-dependent value,
so its valid same-statement witness differences stay in the target space;
they must not be removed with the discarded random-mask generator.

The existing witness-coupled containment interface (fields around lines
250–300) is preferable to demanding full ambient rank: it records the legal
initial/terminal-conditioned sumcheck fiber, compatibility pivot sources
and rows, semantic-kernel coefficients and sparse/dense guards. Those maps
must be regenerated for the new terminal functional, not reused numerically
after the semantic change. First establish the actual dependence on mask
randomness before assuming it is a linear matrix problem. Successful ranks
on fixed schedules can falsify leakage gaps and supply concrete minors; an
adaptive full-view simulator and its challenge/conditioning law remain a
separate proof obligation. No dense rank job was run in this continuation.

## What this does not establish

This is a deterministic mask/layout interface, not a full-view ZK simulator,
entropy-conditioning argument, translated Rust refinement, semantic sumcheck
soundness theorem, or extraction theorem. In particular:

- At non-Boolean opening points, mask additions legitimately change the
  semantic polynomial and proof responses; no off-domain equality with the
  old protocol is asserted.
- The actual generator's new witness-dependent output distribution and all
  adaptive OOD/final/query disclosures require their own privacy analysis.
- Root's implementation must freeze the inverse and new profile before C1,
  preserve canonicality, recompute the initial mask claim from the final
  table, and execute all repaired semantic/image/row/query checks.
- Byte neutrality remains the existing 40,282-byte model, not a proof that
  the additional arithmetic is CU-neutral. No new CU measurement is made here.

## Appendix: literal packed-terminal insertion

`PositiveTerminalInsertion.lean` is a separate **kernel-checked** bridge for
the research wrapper's `composition_delta` / `terminal_delta`. It consumes
the old V7 arithmetic theorem, not a newly assumed pack correspondence.

The source order is pinned by
`pair_forest_semantic_terminal.rs:1143–1182,1267–1274`: four packed Poseidon
lanes, 24 packed semantic lanes and the Copy accumulator. The existing
semantic function ends by adding two scalar residuals at indices 92/93;
the source count is 94 and its final two packed slots are padding. The
research addition at source index 94 occupies group 23, slot 2. That pack
crosses the other 23 semantic packs and four Poseidon packs, giving theta
exponent 27. The copy claim remains the same initial accumulator.

The leaf reuses `V7PairForestCuArithmeticEquivalences.packBase4` and its
shared-selector identity, instantiated with the cached exact QM31 tower.
It additionally models **all four signed limb accumulators** of the current
`field.rs:960–998` packer and proves their field interpretation equals that
map for arbitrary QM31 inputs. The old base-input-only coordinate synthesis
theorem would not suffice for an off-domain selector times a cubic residual.
Canonical `u64` accumulation/reduction and actual source translation remain
distinct from this field-coordinate identity.

The proof uses a symbolic reverse-Horner accumulator lemma, not a reduction
of 29 expanded coefficients. Adding a value to the last pack transports
through a prefix of length `n` as multiplication by `theta^n`. It then
specializes the actual 23+4 lengths, proves the wrapper's square-chain
`theta16*theta8*theta2*theta = theta^27`, and transports through

```text
mask + eta * (eq * composition + mu * H + mu * mu * inactiveH).
```

The proved `positive_terminal_insertion` endpoint is exact addition of
`eta * eq * theta^27 * pack[0,0,selector*(r*c*inverse-1),0]`.
It assumes neither that the new residual vanishes nor that the existing
ordinary relation is correct. Zero challenges and arbitrary QM31 claims
are included; this algebra does not assert every challenge rejects a
false claim. The unchanged terms are the existing expression evaluated on
the **same current proof claims**, not the original protocol's distinct
masked table or transcript.

No new degree-14 ceiling is claimed here: the wrapper's actual point maps
and their individual degree obligations require their own instantiation.
Likewise this deterministic equality is not an additional soundness error
term, an accepted-to-constraint theorem, a privacy simulator or a CU result.

### Focused insertion evidence

| Target / changed attempt | Exit | Wall | Peak RSS | Swap | Evidence |
|---|---:|---:|---:|---:|---|
| Missing V7 pack-equivalence olean export | 0 | 12.68 s | 5,629,411,328 B | 0 | [export](experiments/positive-terminal-pack-export-v1.log) |
| v1, cache namespace lookup failure before elaboration | 1 | 1.94 s | 1,182,449,664 B | 0 | [v1](experiments/positive-terminal-insertion-v1.log) |
| v2, four nested pack projection goals | 1 | 13.39 s | 5,517,099,008 B | 0 | [v2](experiments/positive-terminal-insertion-v2.log) |
| v3, generic projection rules still leave those goals | 1 | 9.84 s | 5,517,312,000 B | 0 | [v3](experiments/positive-terminal-insertion-v3.log) |
| v4, typed tower projections, complete endpoint / 11 audits | 0 | 12.32 s | 5,653,528,576 B | 0 | [v4](experiments/positive-terminal-insertion-v4.log) |

The cache-only fix creates research overlay symlinks for the exact audited
transitive dependencies: Lean otherwise chooses the local `AspisFormal`
namespace containing the exported V7 leaf and cannot see the cached tower.
No dependency was rebuilt. The mathematical fix adds exact typed real/imaginary
multiplication projections, each proved by `rfl`, so the simplifier does not
have to infer both nested tower parameters after basis-constructor reduction.
This is a sparse algebraic rewrite, not increased memory limits or concrete
field enumeration. Two unused-simp-argument warnings remain in the green log;
there are no errors or `sorryAx`. Every audited result uses a subset of
`propext`, `Classical.choice`, `Quot.sound`.

Final source SHA-256
`57d294af1f91039cc397931301d9fde808d100c0297bc1511549b7880e4e0ce5`;
olean `36102e188126f736d09bd215528a3029e786482a651d06804a6b19c9ba5d355b`.
The successful log records the inherited source/olean chain, research source
pin, Lean/mathlib versions, and hashes of the actual Rust packer, terminal
and research wrapper being modeled. Runner syntax and `git diff --check`
passed. With the existing exported cache and a fresh log:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_positive_terminal_insertion.sh leaf docs/research/v8-no-work-100-20260907/experiments/positive-terminal-insertion-recheck.log
```

Use `cache` mode first only if the V7 olean is absent. These are focused,
serialized local checks under the same 7-GiB aggregate guard, not a full
formal manifest replay or Rust-to-Lean extraction. No source/production,
transaction-CU or byte-layout change is made by these mathematical files.
