# J5 circle source and sampler mapping

This is a source-pinned mapping of the current two circle challenges to the
older R0P circle sampler lemmas. It records literal types, rows, conversions,
and hypotheses. It does not establish that a current Rust execution satisfies
the old Lean sampler identities or any soundness conclusion.

The original Rust/R0P source inventory was inspected at historical revision
`c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`. The later selected mathematical
challenge map is recorded separately below; this historical base remains the
provenance for the original source inspection.
The current two-fold row mapping is row 25 = `z0`, row 26 = `z1`; row 26 is
also the deterministic reseed boundary in the unified Lean sampler. The Rust
source assigns `CircleRow::First` to 25 and `CircleRow::Second` to 26.

## Current Rust value construction

`crates/aspis-r1-cost-probe/src/sampler.rs:8-23` defines
`qm31_sample(block: &[u8; 32]) -> QM31`: eight little-endian `u32` words are
reduced in four passes to four base-`P` digits, then assembled into two
`CM31` values and a `QM31`. At lines 94-101,
`circle_sample(block, row) -> SecureCirclePoint` applies
`secure_ood_circle_point_from_parameter(qm31_sample(block))`; on error it
chooses `circle_fallback_point(0)` for `First` and `circle_fallback_point(1)`
for `Second`.

The underlying map in `crates/aspis-core/src/circle.rs:35-45,55-65` forms
`x = (1 - t²)/(1 + t²)` and `y = 2t/(1 + t²)`, rejecting a singular
denominator and parameters whose `c1` component is zero. The fallback
implementation in `crates/aspis-core/src/transcript.rs:282-295` maps the
row-specific fixed QM31 parameters through the same secure map. The separate
reference transcript method at lines 498-515 has the same one-parameter,
fixed-fallback shape.

`r1_wire::circle_validated` (`crates/aspis-r1-cost-probe/src/r1_wire.rs:228-242`)
accepts only validated records 25 and 26, maps those indices to First and
Second, obtains the sample block, and calls `circle_sample`. The reference
method at lines 249-262 applies the same row check to framed bytes. In
`r1_semantic::verify_observed` (`crates/aspis-r1-cost-probe/src/r1_semantic.rs:127-130`),
the verifier reads `z0` at row 25, decodes `before_z1` from row 26, reads `z1`
at row 26, and rejects when `z0 == z1` at lines 152-154. These functions
expose the raw field-sample-to-point construction. A later R1 mathematical
bridge, `SelectedChallengeMap.lean`, now proves the selected model’s row-25/26
circle conversions (`circle_parameter_rows`, `first_circle_view`, and
`second_circle_view`). Those theorems connect the selected Lean challenge
model to the existing R0P total circle maps. They do not prove that current
Rust execution refines the selected model, or that Rust row-byte decoding and
fallback/error branches agree with it.

## Current Lean sampler types

`TranscriptView.lean:12-24` defines `Value Cv` with constructors
`.ordinary : Cv → Value Cv` and `.queries`; `Challenge Cv` is
`Value Cv × State`. `liftChallenge` wraps a duplex challenge as
`(.ordinary ch.1, ch.2)`. It has no circle-point constructor.

In `UnifiedSampler.lean:53-70,83-101`, the generic `p.σ` has type
`Nat → State → Cv`. For a payload at row 25, `row_ordinary` reduces the
sampler to `DuplexSamplers.plain p (absorb p 25 P m) 25 liftChallenge`.
`DuplexSamplers.plain_eval` (`DuplexSamplers.lean:33-38`) shows the sampled
value is `p.σ 25` at the squeeze answer. Row 26 instead uses
`DuplexSamplers.reseeded`; `reseeded_eval` (`DuplexSamplers.lean:50-58`)
uses the same kind of raw value `p.σ 26` but puts the deterministic reseed
answer in the challenge's state coordinate. `UnifiedSampler.row_reseed` and
`UnifiedPayloadStep.reseed_step` make this extra address/state edge explicit.

The generic sampler parameter is generic in `Cv`; its row-shape theorems alone
do not identify `p.σ 25` or `p.σ 26` with a circle point. The separate
`SelectedChallengeMap` specializes the selected mathematical model and proves
the `qm31Sample` and `circleSample0/1` equalities described above. The present
classifier in `UnifiedEventDensity.lean:28-53` explicitly returns `False` at
rows 25 and 26. Its density theorem has no `hσ25` or `hσ26` premise; its
circle-independent bounds begin at row 27. Thus the generic sampler facts
establish row shape, the selected-map bridge supplies the model conversion,
and the Rust-to-Lean/refined-classifier links remain open.

## Reusable legacy Lean facts and their hypotheses

`R0P.SemSource.CircleParam` is the exact-tower `QM31Exact`, and
`circleSample0/1 : State → Point WideExact` are defined in
`R0P/CircleSampler.lean:25-29,129-189`. They apply `qm31Sample` and then the
row-specific `circleSampleParameter0/1`. That parameter map uses the rational
circle map when `t.im ≠ 0` and returns the selected fallback when `t.im = 0`
(`:175-189,191-198`). The formal model records that
`circle_fallback_point` is the corresponding distinct, non-base-rational
fallback pair (`:139-165`).

The point predicates are `z0Bad' z := z0Bad circleFallback1 z` and
`z1Bad z0 z1 := z1Bad z0 z1` at `CircleSampler.lean:223-228`; the underlying
`z0Bad` and `z1Bad` definitions are in
`docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean:58-60`.
`circleSample0_mass` (`CircleSampler.lean:298-312`) bounds the mean indicator
of `z0Bad' (circleSample0 s)` by `(1 + deltaQ) / P^4`. It follows from the
one-element bad-parameter fiber and the `qm31Sample_mass_slack` sampler bound.
`circleSample1_mass` (`:315-329`) has the same bound for
`z1Bad z0 (circleSample1 s)`, with the required premise
`hz0 : z0 ≠ circleFallback1`. `circleBad1_fiber` (`:240-248`) also uses this
premise to exclude the second sampler's rejected-parameter fallback.

The row-transfer APIs give the exact sampler equalities needed to invoke
those mass lemmas:

- `R0P.MaskD2Glue.circle_row25_D2` (`MaskD2Glue.lean:127-141`) requires
  `∀ a, p.σ 25 a = .circle (circleSample0 a)` and transfers to
  `circleSample0_mass`.
- `no_hit_last_circle_ne_fallbackZ` (`MaskD2Glue.lean:143-161`) requires a
  row-26 prefix whose last record contains `.circle z0` and the explicit
  no-hit premise
  `¬ hitFrom (sourceDataZ maskClaims B) Q.statement [] Q.rounds`; it derives
  `z0 ≠ circleFallback1`.
- `R0P.MaskD2Glue.circle_row26_D2` (`:163-184`) requires
  `∀ a, p.σ 26 a = .circle (circleSample1 a)` and the preceding prefix/no-hit
  hypotheses. It then applies `circleSample1_mass z0 hz0`.

The unmasked `R0P.SemD2Glue` wrappers use the same mass statements but the
older row numbers 24 and 25 (`SemD2Glue.lean:603-627,761-837,888-972`). The
masked wrappers have row numbers 25 and 26, matching the current Rust indices,
but their `Chal.circle`, `SemMsgZ`, `sourceDataZ`, and typed-prefix interfaces
are not the generic `TranscriptView.Challenge Cv` model.

## Exact boundary

To use the old circle masses for the current Rust execution, a source bridge
is still needed from the raw block-derived parameter and fallback conversion
to the selected mathematical model, together with the row-specific sampler
equation (including the `Value.ordinary`/circle representation). The second
mass also needs the no-hit-derived `z0 ≠ circleFallback1` premise in the old
typed prefix. The selected-map theorems establish the model-side conversion,
but not these Rust or old-prefix links. In particular, row 26's reseed state
coordinate is not its circle value: the legacy mass concerns only the sampled
point/value.

## Source hashes

| Source | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-core/src/circle.rs` | `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` |
| `crates/aspis-core/src/transcript.rs` | `9bd74c66a28567e4d964896b7e2d7c0ac79840565d44b561747879868bdd9179` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `docs/research/100bit-spend-path-20261013/lean/TranscriptView.lean` | `bce7a74ce7e9ed7c16aa9248b4c808d45847d8e7c455457086f976b65c1b5798` |
| `docs/research/100bit-spend-path-20261013/lean/DuplexSamplers.lean` | `6ae5ba2277f2881deb909fa60667dab008be0a02b2d55f9ec5c20f698fa5e4a3` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedEventDensity.lean` | `b552274d799b3b192daafee66287c74496699304e72ec89a2159f276a3b5da89` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedSemanticDensity.lean` | `db2457d02da3ce58cec52092eab5cfbccdb4f820ed285a451c9dceb6223a0667` |
| `docs/research/100bit-spend-path-20261013/lean/SelectedChallengeMap.lean` | `36bcd2bb277dcb2b34564656c71ebb7b14742c584ce931328a2ad1dbe03e5aad` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean` | `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean` | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2Glue.lean` | `223aba01f619245855e513c552c17a027e7d1cf427fe227a5bf0edacd4ef91a4` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD2Glue.lean` | `c0d9044c08be9cd252224ebc460dbca98898bc22747702ea5ca52d2983b5f910` |
| `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean` | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemSource.lean` | `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024` |
