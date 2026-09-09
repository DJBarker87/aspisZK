# Positive transfer: binding the added packed residual

Research pin: `bbca32e0e30be2c489c6437dd670da164e6d852f`. This continuation changes no Rust, protocol default, transcript or proof body. It audits the already opt-in positive-transfer residual. The focused Lean leaf is kernel-checked with standard axioms only; its precise source boundaries are retained below.

## Source result

The new residual cannot deterministically cancel the old two scalar residuals on a canonical base-valued Boolean trace. More specifically, at row 1014 the old two residuals vanish by their **public selector supports**, without assuming asset correctness. Hence the last packed semantic lane at that row is exactly

`u * (recipient * change * inverse - 1)`.

It is zero precisely when the product-inverse equation holds, even if the supplied values in that row are arbitrary QM31 elements. This is a last-pack statement, not an implication from an accepted sumcheck or an arbitrary off-domain terminal value.

| Source | Literal selected transfer expression | Fields/timing |
|---|---|---|
| `pair_forest_semantic_terminal.rs:1165–1181`, lane 92 | `selector(44) * (C1_z[1] - asset_id)` | Only C1 and public M31 asset; no lambda, chi, H/G or theta |
| Same, lane 93 | `(selector(508) + selector(460)) * (C1_z[1] - asset_id)` | Transfer branch; withdrawal's distinct scalar expression is not covered |
| `positive_transfer.rs:71–93`, new lane 94 | `selector(1014) * (C1_z[1] * C1_succ[1] * C1_z[3] - 1)` | Reserved inverse was installed before the C1 commitment |
| `add_preweighted`, source starts 92, two slots | `[lane92, lane93, 0, 0]` in semantic pack 23 | Digests occupy 84–91, groups 21/22; earlier lanes do not write group 23 |
| Opt-in terminal delta | Adds slot 2 in semantic pack 23 | Existing insertion proof places this pack at theta exponent 27, not an independent extra theta lane |

These are zero-based source indices: the old 94 source residuals occupy 0–93; the research-only addition is index 94, within the existing 96-slot capacity. Slot 95 remains zero padding. This audit does not change the production registry; the existing opt-in research profile framing binds the changed semantics.

At a Boolean point whose ten coordinates are the row's MSB-first bits, all row selectors are M31 zero or one. Canonical recovered **semantic message coefficients**, not raw LDE samples misidentified as coefficients, make the C1 evaluations M31-valued. The actual `lift_m31` is the nested constructor `(a,0,0,0)` in the maintained tower `i²=-1`, `u²=2+i`.

Consequently the four inputs `[a,b,p,0]` at a Boolean row, with arbitrary base-field `a,b,p`, pack to the literal coordinates `(a,b,p,0)`. Zero of that element implies all three residuals are zero. This derives separation from the actual tower representation; it neither chooses a convenient basis nor assumes the old asset residuals vanish.

There is an even narrower source-structural argument at the positivity row. Rows 44, 508 and 460 have MSB zero, while row 1014 has MSB one. Each old selector therefore has a zero factor; the new selector's ten factors are all one. This does not use base-fieldness of the three claimed values or assume their decoded correctness. It only uses the specified Boolean row and last-pack expression.

## Causality and what this does not establish

`payment_extraction.rs:48–55` fixes C1 before lambda/chi, then absorbs C2 before `begin_state_only_zerocheck`. That routine samples theta, ten zerocheck-point coordinates, then mu; eta follows in the masked sumcheck. C2 may depend on lambda/chi. Neither old scalar residual 92 nor 93 reads C2, lambda or chi. The new residual is also a C1-only expression. Those facts do not make a reconstructed post-challenge C1 candidate pre-challenge by assertion: an actual recovery/source bridge must establish the needed earlier fixed object.

Off-domain values are generally QM31, not M31. The proof deliberately includes the identity

`pack[-u*w, 0, w, 0] = 0`

for arbitrary QM31 `w`. Thus four arbitrary extension-valued slots are not independent. Canonical QM31 byte parsing does not fix this. The new theorem is applicable on the Boolean source constraint table, or directly at the explicit Boolean row 1014, **not** by retroactively interpreting arbitrary sumcheck/OOD claims as base values.

The full 29-lane theta combination can also cancel at an exceptional theta. Last-pack zero must follow from a valid semantic/zerocheck argument with its actual fixing boundaries, or be an explicit deterministic premise. The current leaf supplies no additional probability, does not assert theta cancellation never occurs, and does not replace the existing sumcheck, row/image or query checks.

## Proof/source interfaces

| Interface | Status/scope |
|---|---|
| Literal QM31 packer to maintained `(1,i,u,iu)` map | Reused `PositiveTerminalInsertion.literalPack_eq_tower_map` and V7 `packBase4`; source-shaped field formula, not a new Rust machine translation |
| Base input packing has literal four coordinates | New `literalPack_base_coordinates` and `base_pack_zero_iff`; no old-residual-zero premise |
| Selector product, base lift and actual target bits | New symbolic finite product proofs; only three ten-bit MSB comparisons reduced concretely |
| Transfer lanes 92/93 plus 94 on base-valued Boolean rows | New `source_base_pack_zero_iff`; actual selected field expressions, no lambda/chi input |
| Row 1014 last-pack zero implies inverse equation | New `row1014_pack_binding`, deriving old-selector zeros rather than assuming them |
| Rust `Selectors::expand` high[6]/low[4] array implementation equals the ten-factor mathematical selector | Source-inspected, **not translated by this leaf**. The loop recursively multiplies each parent by a coordinate or its complement; `row` multiplies `high[row>>4]` by `low[row&15]` |
| Canonical bytes → recovered C1 message table → actual Boolean MLE claims | Existing recovery/source obligations remain; this file does not parse bytes or assume all accepted tables recover |
| Actual accepted proof → all relevant packed Boolean constraints zero | Still requires the causal semantic/zerocheck and source connection; not discharged by packing algebra |
| Inverse equation → decoded positive amounts/payment endpoint | Prior `SelectedTransferPositive` and value/copy/decoder bridges supply their stated conditional implications; this file does not assume validator acceptance |

The old `V5ExactTowerPacking` supplies the same maintained four-coordinate basis interpretation, but was not imported/rebuilt: the existing V7/research literal full-QM31 packer already supplies the necessary exact coordinate formula. Old 20-pack or 25-total-lane statements are not silently ported to the current 24 semantic / 29 total lane grammar.

## Evidence and costs

The successful focused replay is [positive-pack-binding-v2.log](experiments/positive-pack-binding-v2.log): exit **0**, **17.17 s** wall time, **5,562,793,984 B** peak RSS, **zero swaps**. All eleven `#print axioms` audits use only `propext`, `Classical.choice` and `Quot.sound`; no errors, warnings, `sorryAx` or new axioms. This is a kernel-checked algebraic result, not a Rust/Aeneas translation or runtime experiment.

The [runner](experiments/run_positive_pack_binding.sh) verifies pinned source/cache imports, reuses the already checked terminal-insertion olean, and stops at a 7 GiB process-tree RSS guard. No dependency build or unchanged previous Lean leaf was replayed. Toolchain: Lean `4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Source/cache provenance for the reused V7 pack and literal tower imports is recorded in the successful log.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_positive_pack_binding.sh \
  /absolute/path/to/a-new-positive-pack-binding.log
```

The runner requires a new log path and an explicitly available serialized local slot. Its exact focused command is `lake env`'s pinned Lean environment followed by `lean -M7000 -R <experiments> -o <experiments>/PositivePackBinding.olean <experiments>/PositivePackBinding.lean`.

| Artifact | SHA-256 |
|---|---|
| `PositivePackBinding.lean` | `f2332636ff75ac7b397f9fabd7b6479f1df4c63bd071f14013200badd4edea69` |
| Successful `PositivePackBinding.olean` | `3d5b74e3208f993f5aaaa283a128ac586ff5af5e19fe63bc7017d71c8dbaa912` |
| Reused `PositiveTerminalInsertion.lean` | `57d294af1f91039cc397931301d9fde808d100c0297bc1511549b7880e4e0ce5` |
| Reused `PositiveTerminalInsertion.olean` | `36102e188126f736d09bd215528a3029e786482a651d06804a6b19c9ba5d355b` |

The preserved `positive-pack-binding-v1.log` is a failed diagnostic, not a retained proof result: exit 1, 23.15 s, 5,476,843,520 B peak RSS, zero swaps. Its two failures were a base-lift subtraction `rfl` and missing normalisation of a four-entry vector. The replacement uses coordinate simplification and the vector's explicit cases; it changes no theorem hypotheses or mathematical claim. Its `sorryAx` diagnostics arise from those unsuccessful elaborations and cannot serve as an axiom audit for a claimed completed leaf.

The body remains the existing 40,282-byte maximum model. No verifier operations or messages were added by this proof. This is not a new CU, proving-time, full-view privacy, resource-bounded Fiat–Shamir or 100-bit global security measurement.

The next use is to compose the repaired positive Boolean constraint with a source-connected semantic-lane extraction result, while keeping the actual C1 fixing boundary and scalar batching error visible. A standalone last-pack theorem is not the completed semantic extraction endpoint.
