# J1 circle-row density reuse inventory

This is a source/API inventory for the two circle-sampling positions. It records existing mathematical lemmas and the current literal-row projections; it does not establish their composition into a protocol classifier or a security bound.

## Current selected rows

`SelectedTranscriptParams.params` installs `SelectedChallengeMap.sigma` as its challenge map ([SelectedTranscriptParams.lean](../lean/SelectedTranscriptParams.lean), lines 40–54; SHA-256 `489f8b49c6a102f85c511ad4f4907dbeca479322b7184a563eda8c4a17c2dce0`). The selected map's default branch is `semChal`; consequently rows 25 and 26 both map a state to `semChal s`. `rhoOf` projects the resulting `WideExact` value to the QM31 real component. The checked equalities are:

- `SelectedChallengeMap.circle_parameter_rows`: `rhoOf (sigma 25 s) = qm31Sample s ∧ rhoOf (sigma 26 s) = qm31Sample s`.
- `first_circle_view`: `circleSampleParameter0 (rhoOf (sigma 25 s)) = circleSample0 s`.
- `second_circle_view`: `circleSampleParameter1 (rhoOf (sigma 26 s)) = circleSample1 s`.

These are in [SelectedChallengeMap.lean](../lean/SelectedChallengeMap.lean), lines 11–56 (SHA-256 `36bcd2bb277dcb2b34564656c71ebb7b14742c584ce931328a2ad1dbe03e5aad`). The rank bridge is [SelectedSamplerRanks.lean](../lean/SelectedSamplerRanks.lean), where `qm31_eq` identifies `qm31Rank (reduce (stateRank s))` with old `qm31Sample s` (lines 32–38; SHA-256 `5e80166fd121340b45df200ee9b14b51e83895ff8382a2e95a59f9f793d1bf11`). The sampler's shape is separately represented by `UnifiedSampler.samp`: ordinary payload rows except 0, 26, and 31 use `DuplexSamplers.plain`; row 26 uses `DuplexSamplers.reseeded`, whose returned field challenge is still `p.σ 26` (see [UnifiedSampler.lean](../lean/UnifiedSampler.lean), lines 53–70 and 83–87; SHA-256 `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad`).

The literal transcript stores an ordinary challenge as `TranscriptView.Value.ordinary v` for `v : WideExact` ([TranscriptView.lean](../lean/TranscriptView.lean), lines 16–24). `LiteralTranscript.samp` erases the literal message wrapper and delegates to `UnifiedSampler.samp` ([LiteralTranscript.lean](../lean/LiteralTranscript.lean), lines 16–22, 27–42, 67–71; SHA-256 `2b76b95f5dffb2856f1af3884859d3d8d16e60bf47c0950559fe3c5e44ec4ed6`). [LiteralChallengeRead.lean](../lean/LiteralChallengeRead.lean) defines `ordinaryAt`, with `ordinaryAt_append` and `ordinaryAt_success` for the selected list index; its focused-green source SHA-256 is `37e1456e07326dc33ec30fc6b0e93aa47692eb699d3a76ede57e51473327bdfc` (evidence: `../evidence/lean-literal-challenge-read-20261015/`). This is representation plumbing only. The existing selected challenge map provides the projection from that ordinary value to the old QM31 parameter and total circle map; it does not by itself classify the row's bad event.

## Reusable old circle statements

The old fallback points and total row maps are in [CircleSampler.lean](../../v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean), source SHA-256 `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100`:

- `circleFallbackParameter0/1` are `(0,1)` and `(1,1)` respectively (lines 129–145); `circleFallback0` and `circleFallback1` are their embedded non-rational circle points.
- `circleSampleParameterWith fallback t` maps a parameter with nonzero imaginary coordinate to its circle point, and otherwise returns the supplied fallback (175–189). `circleSample0/1` apply this to `qm31Sample` using fallback 0/1.
- `z0Bad' z := z0Bad circleFallback1 z`, while `circleBad0Pred` and `circleBad1Pred z0` compose the two total maps with the bad predicates (222–228). The imported predicates are `SemStatement.z0Bad fallback1 z := BaseRational z ∨ z = fallback1` and `SemStatement.z1Bad z0 z1 := BaseRational z1 ∨ z1 = z0` ([R0C/SemStatement.lean](../../v8-r0-close-20261007/lean/R0C/SemStatement.lean), lines 58–60).
- `circleBad0_card` proves the first bad parameter set has cardinality at most one (251–256); `circleBad1_card z0 hz0` proves the same for the second set, requiring `hz0 : z0 ≠ circleFallback1` (258–264).
- `circleSample0_mass` gives `mean (indicator (z0Bad' (circleSample0 s))) ≤ (1 + deltaQ) / P^4` (298–312). `circleSample1_mass z0 hz0` gives `mean (indicator (z1Bad z0 (circleSample1 s))) ≤ (1 + deltaQ) / P^4` (315–329). Both are modulo-sampler bounds, not ideal uniform-circle bounds; `deltaQ` is the modulo slack from `qm31Sample_mass_slack`.

The ideal full-circle alternatives are in [R0C/CircleRows.lean](../../v8-r0-close-20261007/lean/R0C/CircleRows.lean): `z0_density_le fallback1` and `z1_density_le z0` each bound the corresponding event under uniform `Point K` by `(2^31+1) / Fintype.card (Point K)` (lines 58–73), and `chord_conditions` derives distinctness/non-rationality from the two event exclusions (77–80). The selected sampler instead reuses the modulo `circleSample*_mass` theorems above.

The old prefix/D2 transfer is in [MaskD2Glue.lean](../../v8-r0-sem-proof-20261008/lean/R0P/MaskD2Glue.lean), source SHA-256 `c0d9044c08be9cd252224ebc460dbca98898bc22747702ea5ca52d2983b5f910`:

- `circle0_roundBadZ Q m c hr h` at rows 98–107 says a row-25 `roundBad` event has message `.beforeZ0 y`, circle challenge `z`, and `z0Bad' z`.
- `circle1_roundBadZ Q m c hr h` at 109–119 says a row-26 event has the prior last record `.beforeZ0 y, .circle z0`, current message `.beforeZ1 y0`, circle challenge `z1`, and `z1Bad z0 z1`.
- `circle_row25_D2` (127–141) and `circle_row26_D2` (163–191) turn those shapes into the row bounds, but require the old `duplexRowsZ`/`doomed` context and an explicit sampler identity `hσ`. The second theorem also splits on whether that prior circle record exists.
- The exact needed non-fallback fact is `no_hit_last_circle_ne_fallbackZ` (143–161): with `Q.round = 26`, `hprev : Q.rounds.getLast? = some (.beforeZ0 y, .circle z0)`, and `hno : ¬ hitFrom (sourceDataZ maskClaims B) Q.statement [] Q.rounds`, it concludes `z0 ≠ circleFallback1`. `circle_row26_D2` obtains this from `hd.2` before invoking `circleSample1_mass z0 hz0`.

The analogous earlier `SemD2Glue` API is offset by one row: `no_hit_last_circle_ne_fallback` assumes row 25 and the two D2 rows are 24/25 (lines 603–625, 761–974). `MaskD2Glue` is the closer index/API match for current selected rows 25/26, though both remain older source-data and `doomed` classifiers.

## Unresolved connection

The retained selected APIs provide the ordinary challenge read (`LiteralChallengeRead.ordinaryAt`), the positional map (`SelectedChallengeMap.sigma`), rank identity (`SelectedSamplerRanks.qm31_eq`), and total circle-map identities (`first_circle_view`, `second_circle_view`). The old density lemmas require event predicates in terms of `z0Bad'`/`z1Bad`, plus (for row 26) a concrete prior `z0` and `z0 ≠ circleFallback1`. The old D2 wrappers derive their shape and no-hit premise from `sourceDataZ`, `roundBad`, `hitFrom`, and `doomed` on the older `MsgZ` prefix.

No theorem in the cited current files identifies the current literal row-25/26 read with the particular `.beforeZ0`/`.beforeZ1` message payloads and preceding `.circle z0` record expected by those old shape lemmas, or derives the old `hno` premise from the current selected causal classifier. The selected challenge map also needs to be used with the same typed `Point WideExact` event views as the old predicates. Those are explicit model-interface gaps; this note does not select additional premises or assert that either old D2 row theorem applies to the current classifier.


## Current fixed-input density adapter

`lean/LiteralCircleDensity.lean` is focused-green at source SHA-256
`e353554ab952041f34a53113b62840b319c7f41acb073ee81949e8701769e302`;
evidence is in
[`evidence/lean-literal-circle-density-20261015/`](../evidence/lean-literal-circle-density-20261015/).
Attempt e passed after four failed proof attempts; the final compile emitted
five standard axiom reports (`propext`, `Classical.choice`, `Quot.sound`). It
proves row-25 and row-26 fixed-input sampler-density adapters using the
selected challenge-map identities. The row-26 event explicitly retains its
prior `z0` and `z0 ≠ circleFallback1` guard. The theorems do not derive that
guard from the transcript prefix or establish terminal acceptance, full D2/D3,
or source refinement. Attempts a–c were launched from `3944eaa5cfdcfff8867d8a46437c02613366e201`; d–e from
`3c79ec30fa44f408c716bb345050c137e907fa67`.
