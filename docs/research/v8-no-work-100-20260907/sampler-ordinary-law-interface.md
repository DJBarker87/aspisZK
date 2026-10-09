# Ordinary sampler: exact value-mass interface

Source analysis at `ce36c58168987142d3f07e5d8cba00fb7b1dd05b`.
This agent used no compilation or remote action for the source analysis.
The metadata agent separately performed the authorized read-only NUC cache
preflight described below. `OrdinaryPrefixMass.lean` is the intended next
focused file, not a checked result; no implementation is included in this
checkpoint's theorem census.

## The block-discard bridge already exists

Do not rebuild the ordinary decoder correspondence. In
`AspisFormal/AspisFormal/K1/V7Tag73EightRetrySamplerLaw.lean`:

- `Tag73RawStream` is a vector of 32 mathematical `Fin (2^32)` words.
- `tag73RawRun` runs four consecutive eight-retry limb calls on that shared
  word stream, returning the four canonical residues and untouched raw words.
- `SuccessfulTag73RawStream` restricts to successful runs.
- `successfulTag73Values_joint_uniform` and
  `successfulTag73OrdinaryExactLaw_eq_uniform` prove exact uniformity of
  the successful value. They do not turn an abort into a field value.

`V7Tag73EightRetryDecoderBridge.decodeFourLimbs_rawWordsToNat` proves
word-for-word equality with `decodeLimbs 4`, including failure, words used,
and the remaining word suffix. By itself this theorem does not yet implement
discarding the unused words of the final consumed block.

That last step is already proved in
`V7Tag73VariablePrefixGammaFlatRouting.lean`:

- `fourGammaBlocksRawEquiv : (Fin 4 → Digest256) ≃ Tag73RawStream` is
  defined in its Factorization dependency. It is a literal chronological
  block/word and little-endian coordinate equivalence.
- `decodeOrdinaryPrefix_fourGammaBlocksRawEquiv` (line 550) proves the
  **total** equality

  `decodeOrdinaryPrefix (List.ofFn blocks) =`
  `(tag73RawRun (fourGammaBlocksRawEquiv blocks)).map`
  `(ordinaryPrefixDecodeOfRawSuccess blocks)`.

- `ordinaryPrefixDecodeOfRawSuccess` sets `blocksUsed = (wordsUsed+7)/8`
  and `remainingBlocks = blocks.drop blocksUsed`. Thus leftover words in
  the last consumed block are discarded, not forwarded to the next call.
- `fourGammaBlocksRawEquiv_success_iff` identifies the successful events.
- `ordinaryPrefixDecodeOfRawSuccess_exact_value` identifies the decoded
  byte value with `tag73FourLimbsToExact result.1`.
- `successfulRawOrdinaryDecode_run` and
  `successfulRawOrdinaryDecode_value_eq_exact_encoding` give convenient
  successful-subtype versions of the same statements.
- `decodeOrdinaryPrefix_of_matching_consumed_prefix` proves that changing
  only unread blocks leaves value, limbs, words used and blocks used fixed;
  only the returned unread suffix changes.

This is the strongest directly reusable bridge. The name “Gamma” does not
restrict its one-call theorem to nonzero output or to the gamma label.
Conversely, its later three-call routing theorems implement the nonzero
wrapper and cannot be silently substituted for the new nested circle /
distinct-second wrapper.

## Smallest missing one-step theorem

Define the actual one-call exact value on four output blocks by

`value blocks := (decodeOrdinaryPrefix (List.ofFn blocks)).bind`
`  (fun decoded => decodeTagQM31ExactLE decoded.value)`.

Let `successMass` be the uniform finite-coin mass of `value blocks` being
Some; retain its definition as a rational finite count. The desired theorem
is, for every actual QM31 value v,

`avg univ (fun blocks => if value blocks = some v then 1 else 0)`
`  = successMass / (P^4 : ℚ)`.

No closed form for successMass is required to use this theorem. In
particular, it need not replay a limb-abort probability calculation.

The most economical proof uses the stronger constructive result underlying
V7's successful uniform law:
`V7Tag73VariablePrefixGammaFactorization.successfulOrdinaryExactFactorization`
is an equivalence

`SuccessfulTag73RawStream ≃ Tag73OrdinarySamplerSkeleton × QM31Exact`.

The skeleton retains rejection positions, high bits and unused raw words.
Its value projection is exactly `successfulOrdinaryExactValue`. Therefore
each successful value fibre has the same cardinal, and the total successful
cardinality is that fibre cardinal times P⁴. Combining this with the total
block/raw equivalence gives the rational formula directly, without passing
through ENNReal coercions. This consumes the already proved exact uniform
factorization, not an assumed uniformity or a newly chosen arbitrary map.

For an arbitrary finite target set T, summing disjoint singleton fibres then
gives mass `successMass*T.card/P^4`. For the circle accept predicate and a
target v outside CM31, the `BoundedRetryKernel.mass_eq` inputs become

- `hitLaw`: `u = successMass/P^4`;
- `rejectLaw`: `r = successMass*P^2/P^4`, since only successfully returned
  CM31 values retry; an ordinary sampler failure contributes zero here.

The new checked `SecureCircleParameterDomain.admissible_iff` and exact domain
cardinality supply the CM31/admissible partition. A target inside CM31 has
hit mass zero, not u.

## History and unread coins remain a separate obligation

The one-step value may be followed by an arbitrary update of the prior
history using the actually consumed blocks and decoded result. Its marginal
value law is unchanged. A source-shaped update must see only the consumed
block prefix and a result whose `remainingBlocks` field has been removed or
replaced by `[]`; it must not inspect the padded unread blocks used to define
the four-block finite coin space. Duplex-advance outputs also belong to the
consumed history, and may be included as separate fresh-coin coordinates.

For example, when all first four words are accepted, the ordinary call
consumes one block, discards words 4–7 of that block, and the next ordinary
call starts at chronological block 1. It does not start at raw word 4 or at
the next fixed four-block window (chronological block 4).

`BoundedRetryKernel` samples a new finite coin for every recursive call.
Its marginal hypotheses must hold at every history. Showing the decoder law
on an explicit uniform four-block coin does **not** discharge that condition
for a monolithic transcript: the same underlying tape must be routed at the
actual stopping positions, and fresh squeeze/advance inputs must be justified.
The cached `decodeOrdinaryPrefix_take_blocksUsed` and
`decodeOrdinaryPrefix_of_matching_consumed_prefix` are deterministic inputs
to that future routing proof, not statements that unread coins are fresh.

Do not condition on the eventual OOD identity, accepted suffix, candidate
selection or proof success. The proposed one-step equation is unconditional
over its explicit finite raw coins, with immediate sampler aborts retained.

## Cache/import boundary

The minimal proof imports are `V7Tag73VariablePrefixGammaFlatRouting` and a
small research rational-average interface (`BoundedRetryKernel` if its hit /
reject spellings are used). FlatRouting transitively brings the exact
EightRetrySamplerLaw, EightRetryDecoderBridge, SamplerExactValue,
RawNonzeroSamplerFactorization and VariablePrefixGammaFactorization.

The Domain v2 manifest (851 pinned entries) contains none of FlatRouting,
VariablePrefixGammaFactorization, EightRetryDecoderBridge or EightRetrySamplerLaw.
The metadata agent's separate authorized read-only NUC preflight subsequently
found their native clean-k16 compiled outputs, but **not a safe drop-in closure**:

- Full FlatRouting would add 38 modules, including SemanticTranscriptBridge.
- It meets 18 frozen overlay boundary modules, with 12 differing native olean
  variants. The mixed import graph has not been checked and was not staged.
- Native TranscriptSchedule source has drifted (hash prefix `1e9ebd…`), whereas
  the frozen overlay retains source `a55c18…` and olean `e37a4e…`. The drifted
  native source must not be substituted for the pinned overlay source.
- The direct EightRetryDecoderBridge closure is substantially narrower:
  EightRetrySamplerLaw, StoppingTimeSampler, and the already-pinned
  DecoderExact / DeployedDecoderFiberCap / Tower / Rejection interfaces.
  This is a dependency-reduction opportunity, not a completed compatibility
  certificate.

Accordingly, do not import the newly located full native FlatRouting graph
into the frozen workspace. The recommended next split is:

1. A focused raw unconditional-mass leaf using the narrow eight-retry law.
   Its equal-fibre construction needs only the ordinary part of the V7
   factorization, not the nonzero wrapper or whole GammaFlatRouting module.
2. A new, explicitly attributed source port of the small four-block/raw
   equivalence, total decoder commute and byte-value identification, checked
   against the frozen source boundary. Retain the actual rounded block discard
   and consumed-prefix theorem, rather than replacing them with a correspondence
   hypothesis. This stage remains open until checked.
3. Only then the source-shaped `OrdinaryPrefixMass` consumer and, separately,
   the history/flat-tape routing needed for recursive sampler use.

No cold dependency build, native/frozen cache mixing, or enlarged-cap replay
is authorized by this proposal. No source or artifact was staged during this
preflight. All old green sources remain untouched.

Inspected source SHA-256 pins (K1 paths are under `AspisFormal/AspisFormal/`):

| Source | SHA-256 |
|---|---|
| `K1/V7Tag73EightRetrySamplerLaw.lean` | `dfb490b1bfbce4abe894e1809ec8d933acb55dbc5f6e5eb1de5b6942e5b5941e` |
| `K1/V7Tag73EightRetryDecoderBridge.lean` | `027dc6b1a91fe9b21bdd7db6929fb70da4aa204745e8cc39bbc4cd5fb48673e4` |
| `K1/V7Tag73VariablePrefixGammaFactorization.lean` | `5ca77d543500dac67c95883dfe6a39173fc9a49ed792f7e3c8c16322462f1aeb` |
| `K1/V7Tag73VariablePrefixGammaFlatRouting.lean` | `f99a9cd8160535f3bab41c6bb87bc775ff7d39cabe431b00aed1a0981f214041` |
| `K1/V7Tag73RawNonzeroSamplerFactorization.lean` | `7ea2e56e4ce7458a5bb6e34e4251690ca4a1e5c6890c9c3ffa675c51ec1a2fe1` |
| `experiments/BoundedRetryKernel.lean` | `78d6ac88c22571570e2b7407949011e0b77795377446dce48534ae7a283d0da8` |

The native outputs reported by the metadata preflight begin `6a662071…`
(EightRetrySamplerLaw), `1039d5af…` (EightRetryDecoderBridge), `3bb3a8b7…`
(GammaFactorization), and `0d6fc74d…` (GammaFlatRouting). These are discovery
identifiers only, **not** a provenance certificate for a permitted mixed build.
