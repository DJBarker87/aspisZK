# J5 circle-row reuse inventory

This is a source-pinned inventory of the existing circle sampler facts and
the current unified sampler shape. It records interfaces and premises only;
it does not select a classifier or claim that the old round bounds apply to a
current protocol execution.

## Existing circle predicates and sampler bounds

In `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean:58-60`,
`z0Bad fallback1 z := BaseRational z ∨ z = fallback1` and
`z1Bad z0 z1 := BaseRational z1 ∨ z1 = z0`. The old row-specific alias
`R0P.SemSource.z0Bad' z := z0Bad circleFallback1 z` is in
`docs/research/v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean:222-228`.
Thus `¬ z0Bad' z0` implies `z0 ≠ circleFallback1` directly by unfolding the
disjunction. The companion old two-row bad event is `z1Bad z0 z1`.

`R0P.SemSource.circleSample0_mass` at `CircleSampler.lean:298-312` states

```lean
mean (fun s : State => indicator (z0Bad' (circleSample0 s))) ≤
  (1 + deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4
```

`circleSample1_mass` at `CircleSampler.lean:315-329` has the same bound for
`z1Bad z0 (circleSample1 s)`, with the explicit premise
`hz0 : z0 ≠ circleFallback1`. Both masses use `qm31Sample_mass_slack` and
`event_mass_le`, with a one-element bad-parameter fiber. Supporting facts are
`circleBad0_card`, `circleBad1_card`, and `circleSample0_bad_iff` at lines
258-281. In particular, the second fiber proof `circleBad1_fiber` at lines
240-248 requires that same `hz0` to rule out the rejected-parameter fallback.

The old round-level transfer lemmas are in
`docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2Glue.lean`:

- `circle_row24_D2` (lines 761-837) assumes the old prefix has round 24,
  `duplexRows B budget).doomed P T'`, and
  `∀ s, p.σ 24 s = Chal.circle (circleSample0 s)`. It bounds the
  independent sampler's probability of ceasing to be doomed after one
  message by the first circle mass.
- `circle_row25_D2` (lines 888-974) assumes round 25, the previous value
  prefix ending in `(.beforeZ0 y, .circle z0)`, the same doomed-prefix
  premise, and `∀ s, p.σ 25 s = Chal.circle (circleSample1 s)`. It derives
  `z0 ≠ circleFallback1` from the no-hit component of `doomed`, then applies
  `circleSample1_mass`.
- The helper `no_hit_last_circle_ne_fallback` (lines 603-627) takes a value
  prefix of round 25, that last-row fact, and
  `¬ hitFrom (SemD3Glue.sourceData B) Q.statement [] Q.rounds`; it concludes
  `z0 ≠ circleFallback1`. It constructs the forbidden hit by appending the
  last z0 row to the no-hit prefix. This is a source-data `hitFrom` premise,
  stronger in shape than merely a typed circle value.

The standalone mass lemmas live in `R0P.CircleSampler`; its direct imports are
`R0P.SemD2`, `R0C.CircleRows`, and `AspisV8R19.SamplerCirclePolicy` (lines
1-3). The D2 round wrappers live in `R0P.SemD2Glue` and import its larger
semantic/D2 cone. These source paths identify the checked declarations; this
inventory does not assert a current cached-object or build-cost status.

## Current R1 row 25 and row 26 sampler shape

`docs/research/100bit-spend-path-20261013/lean/UnifiedSampler.lean:53-70`
defines `samp` over `p : FS2.Duplex.Params M Cv L`. The parameter projection
has the literal type `p.σ : Nat → State → Cv` from
`docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean:61-72`.
`TranscriptView.Challenge Cv` is `Value Cv × State`, and
`liftChallenge (v,s) = (.ordinary v,s)` in
`TranscriptView.lean:21-24`; this wrapper does not itself produce the old
`R0C.SemStatement.Chal` constructors.

- At index 25 with `.payload m`, `UnifiedSampler.row_ordinary` (lines 94-101)
  reduces to `DuplexSamplers.plain p (absorb p 25 P m) 25 liftChallenge`.
  `DuplexSamplers.plain_eval` (lines 33-38) gives challenge value
  `p.σ 25 (H (squeezeA p (H (absorb p 25 P m))))` and next state
  `H (advanceA p (H (absorb p 25 P m)))`.
- At index 26, `UnifiedSampler.row_reseed` (lines 83-87) reduces to
  `DuplexSamplers.reseeded p (absorb p 26 P m) (OpeningReseedFrame.addr …)
  26 liftChallenge`. `reseeded_eval` (lines 50-58) samples the ordinary
  challenge value from `p.σ 26` at the squeeze answer; the challenge's state
  coordinate is instead the answer to the deterministic reseed address after
  the advance answer. `UnifiedPayloadStep.reseed_step` (lines 46-54) exposes
  that final state.

Therefore a direct use of the old circle mass statements would need a
separate, explicit identification of the current row values with
`circleSample0` / `circleSample1` (and any `Value.ordinary`/old `Chal.circle`
wrapping). The sampler API alone only supplies values in arbitrary `Cv`.
Row 26 also has an extra reseed read after the challenge value; the mass
statement concerns the value sampled by `p.σ`, not that reseed state.

## Source pins

SHA-256 of the cited source files at this inventory:

| File | SHA-256 |
|---|---|
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/CircleSampler.lean` | `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100` |
| `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2Glue.lean` | `223aba01f619245855e513c552c17a027e7d1cf427fe227a5bf0edacd4ef91a4` |
| `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean` | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` |
| `docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean` | `3a2c1330dfd39d59b10cdf1fc68b218432775b855c98e700d1ba938eeac2d88b` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedSampler.lean` | `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad` |
| `docs/research/100bit-spend-path-20261013/lean/DuplexSamplers.lean` | `6ae5ba2277f2881deb909fa60667dab008be0a02b2d55f9ec5c20f698fa5e4a3` |
| `docs/research/100bit-spend-path-20261013/lean/UnifiedPayloadStep.lean` | `a4c579f794fe58946e2001c8228f60e85e139724e4f36dd2d9bd4c253d2b2359` |
| `docs/research/100bit-spend-path-20261013/lean/TranscriptView.lean` | `bce7a74ce7e9ed7c16aa9248b4c808d45847d8e7c455457086f976b65c1b5798` |

## Current literal challenge-list adapter

`lean/LiteralChallengeRead.lean` is now focused-green at source SHA-256
`37e1456e07326dc33ec30fc6b0e93aa47692eb699d3a76ede57e51473327bdfc`;
its evidence is in `evidence/lean-literal-challenge-read-20261015/`. The
module proves that an ordinary value at a list index is preserved by appending
a suffix and can be recovered as an indexed `(message, (ordinary value,
state))` entry. It does not identify that value with an old circle challenge
or establish a prior no-hit condition.

`lean/LiteralCircleDensity.lean` is now focused-green (source SHA-256
`e353554ab952041f34a53113b62840b319c7f41acb073ee81949e8701769e302`; bundle
`evidence/lean-literal-circle-density-20261015/`). It proves fixed-input
density adapters for selected rows 25 and 26 using the selected circle-view
identities and old modulo-sampler mass lemmas. The row-26 event retains
explicit prior `z0` and `z0 ≠ circleFallback1`; the module does not derive
that guard from a transcript/no-hit prefix or establish terminal/source
acceptance, full D2/D3, or source refinement.
