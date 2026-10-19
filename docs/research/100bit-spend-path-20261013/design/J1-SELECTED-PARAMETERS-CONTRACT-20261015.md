# Selected transcript parameters and scope

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`../evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

Lead-fixed continuation of J1.R4, after the public codec and typed cut
extension results in `764bf20a6`. This fixes the mathematical parameter
instance; the source-refinement obligations are not assumed away.

The committed byte-transcript model uses `L = 131072` for hash addresses and
`D = 3717` for encoded row messages. Its message carrier is a byte list of
length at most D, with identity encoding and a length-checking decoder.
Strict row-specific framing, field canonicality and algebraic acceptance are
separate parsers/decision checks. Being in this carrier never means a message
or spend is accepted. The source inventory's largest semantic frame is the
current expanded row 25, with 3712 payload bytes plus a five-byte header.
Opening frames fit this bound too. The older `semantic_wire` row-25 payload
has only 2784 bytes and must not be substituted for the selected `r1_wire`.

The address cap accommodates the inventoried S2 proof hash (124343 bytes),
the 1880-byte ASF8 public-envelope hash, and the smaller transcript/Merkle
inputs. This is a choice of model parameter informed by inspected source,
not an all-input Rust bound theorem. The source proof must establish every
hash input bound before it uses this instance, including rejected executions.
For adversarial inputs above the cap, the formal totalization remains the
empty address as required by the lead decisions.

For rows 0 through 32, the absorb label is the byte `160 + row` (generic
out-of-range labels are reduced modulo 256). The instance has 33 rounds.
The generic IV is zero; the initial C1/public sampler computes the actual
P3 initial state and overrides that placeholder before semantic challenges.
The semantic and opening domains reuse `PublicInitFrame.domain` and
`OpeningReseedFrame.domain`. The opening variant tag is 2 for the selected
S2 cost-probe variant; this is separate from the core envelope's version 4.

`SelectedChallengeMap.sigma` carries the existing embedded QM31 modulo
sample for semantic rows 0–24, the WideExact nonzero sample for gamma at 27,
and the full WideExact sample at 28–30. Row 32 uses the embedded QM31 sample
and projects back to QM31 for rho. Row 31's scalar coordinate is zero and
unused: its actual output is supplied by the separate q22 sampler.

Rows 25 and 26 carry an embedded QM31 parameter, then the typed view applies
the existing row-specific total circle map. The checked first/second circle
view equalities identify these with `circleSample0/1`. They do not replace
the circle bad events, their exclusions, or the point predicates needed by
the old opening view. In particular, the existing combined classifier still
sets these two rows to false and is not the final J5 classifier.

`SelectedSamplerRanks` fixes the byte-position rank and existing field
tuple ranks, proving their agreement with the generic sampler-bound APIs.
`SamplerRepeatedPass` separately connects any number of bounded word-division
passes to the already proved low-digit arithmetic. Neither module proves
that the current Rust loop implements the model. `SamplerBlockRank` and
`SourceSamplerByteRank` now connect the existing Aeneas byte decoder, the
eight decoded words, repeated machine-model division, and the four/eight
Nat digits (including gamma's end-around carry) at the exact block rank.
Digit-to-field interpretation and extracted source-loop execution still
require their explicit connections.

The public statement constructor takes successful model decoding as its
premise, preserves those exact bytes, and fixes the S2 tag. Its public-length
and initialization-frame bounds come from `SemanticPublicCodecComplete`.
The ASF8-to-carrier mapping and source serializer correspondence remain open.
`SelectedSemanticMessages` now embeds the strict row-0–24 payloads into the
bounded raw-message carrier, proves exact decode/re-encode uniqueness, and
maps them into `SemanticPayloadView` with its C2 recovery callback still
explicit. `CircleRecordCodec` and `OpeningRecordCodec` provide strict model
codecs for rows 25–26 and 27–32 respectively. Derivation of the C2 callback
at its commitment cut remains open. These codec interfaces do not
instantiate an accepted idealized word protocol, the classifier, the
commitment compiler or the knowledge extractor.
