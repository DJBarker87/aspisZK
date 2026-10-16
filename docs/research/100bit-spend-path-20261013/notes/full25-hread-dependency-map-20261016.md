# Actual source obligations for full25 completed-message bytes and hread

This is a composition/dependency analysis, not a new Lean result. The source is approved Prepared+tx1_finish revision `e5c186ba3`. The current actual `verify_observed` loop remains an extractor blocker. Strict parsing alone does not establish source transcript identity or actual challenge provenance. No new theorem below is assumed.

## Exact missing caller result requested from A

For success of the **actual complete** `verify_observed D public bytes hash obs`, returning `out : r1_semantic.Verified H`, derive witnesses `pre,t0,t15,t25` such that:

- `PrefixAdapter.parseAccepted bytes = ok (.Ok pre)`; this is the concrete nominal adapter of the accepted actual Rust Prefix parser, not a parser callback.
- `r1_semantic.public_transcript D public hash pre.c1_root = ok (.Ok t0)`; this supplies the serializer-helper success needed by C's checked `PreparationBinding.helper_binding`. Reaching opening `Prepared::new` alone does not supply it.
- `r1_wire.begin D pre t0 = ok (.Ok out.challenges,t15)`.
- `BeginCalls.SemanticRun D pre [15#u8,16#u8,17#u8,18#u8,19#u8,20#u8,21#u8,22#u8,23#u8,24#u8] t15 t25 out.alpha.val`.
- `out.state_before_z0 = t25.state` and the returned transcript's eventual row25/26 calls/carry are the same calls, if full semantic/opening carry is also claimed.

The fourth point must be derived from actual loop success, including the two existing arithmetic folds and first-error checks. It must not be supplied as an assumed theorem. No premise asserting already-equal message bytes, a chosen alpha list, sampler success, individual child-call success or completed decoding is allowed. Arithmetic/parser function boundaries may stay explicitly parameterized where source extraction is unsupported, but the exact source control flow and its error branches must be retained.

A's checked `begin_success` already supplies an ordered `SemanticRun` for rows0–14 and **equality** of its returned q-list to `challengeList out.challenges`; the weaker per-row `q∈challengeList` from `begin_row_provenance` is insufficient to identify challenge order. Concatenation of the two runs gives the ordered25-row source run, with actual state carry at the shared t15 endpoint. The semantic rows0–24 are all sampled QM31; row25/26 circle calls and the row26→opening reseed are necessary for the all33/state-carry claim but not for the25-row hread premise.

## How actual hbytes must be derived

For each successive constructor of that ordered source run, derive:

1. Its exact source `record.framed` from `Prefix.validated_record pre row = ok (.Ok record)` using checked `BeginProvenance.validated_record_bytes`: `record.row=row` and `pre.records.val[row.val]?=some record.framed`.
2. Its three exact Digest32 calls/state update from checked `CallerStep.semantic_step_success`, using that same record and the same before/mid transcript. This supplies absorb, read1, read2, next-row increment and actual q from the sampled read1 block. The log must be built from these witnesses, not selected independently.
3. The raw message byte map is fixed as `frame.val.map ExtractedRecordByteValue.rawByte`. Position0 through24 matches the ordered source rows, so a list-extensionality proof derives

   `rs.map (fun r => r.2.2.1.val) = PrefixAdapter.completedRecords pre`

   for the record list **constructed from that actual run**. Here completedRecords is exactly `(pre.records.val.take 25).map (fun frame => frame.val.map rawByte)`. This is the missing hbytes conclusion, not a new hypothesis.

The bounded `SelectedTranscriptParams.Message` constructor also needs the existing fixed message bound3717. It should be obtained from the parsed row's strict framing/typed-codec bounds (semantic records are≤901 bytes), not an arbitrary length assumption. `validated_record` itself merely projects an array slot; it does not independently re-parse framing. Therefore retain the original Prefix parser success throughout.

## hread composition once the source bytes are proved

`PrefixAdapter.parse_typedFull bytes pre hparse` already gives actual `values : SemanticPrefixCodec.Full` with all three facts on the same source array: decodeFull success, encodeFull equality, and `decodeFrom 0 (completedRecords pre)=some(entriesOf values)`.

Rewrite this decodeFrom fact with the **derived** hbytes above. `SemanticPrefixCompletedAgreement.completed_read_of_decode` then supplies exactly

`SelectedSemanticPrefix.read recoverC2 0 (SelectedCompletedSemantic.pairs T acc 0 rs) = some outPairs`

where outPairs is the existing fixed typed-payload map zipped with the exact same completed challenge list. This is `SelectedCompletedSemantic.semChalsZ_read.hread`. Apply that existing theorem (or `completed_semChalsZ_of_decode`); do not add another parser or a bridge that takes hbytes as a premise. Existing `completed_records` proves completion changes no message bytes, and decoded-length facts prevent silent zip truncation.

This hread success works for any fixed T/acc and callback; it **does not** identify those completed challenges with the actual Rust q's. That stronger identification is a separate, explicit source/address obligation below.

## Actual challenge/address relation still required

Use the fixed state representation `SqueezeOracleBridge.decodeState`, not a new QM31 model. `SourceSamplerByteRank.rank block` is the blockRank of that exact decoded32-byte block. A's `SamplerTransport.sample_coordinates_of_success`/`sample_total` already supplies the current nominal q coordinates and canonicality from actual sampler execution; fixed `toOld→toCurrent→ExtractedCurrentQM31Exact.decode` transports it to the existing exact QM31 tower, embedded in `AspisWideTower.WideExact` as the semantic value. A small coordinate/rank composition may still be required to identify that value with `SelectedChallengeMap.sigma row (decodeState block)`; keep the current accepted coordinate order c0.a,c0.b,c1.a,c1.b.

For each actual source row j, the selected oracle relation must identify:

- flatten(absorbParts before.state tag record.framed) with the exact byte address of `absorbA params (decodeState before.state) (params.lbl j) message.val message.bound`;
- flatten(readParts absorbed 1) with `squeezeA params (decodeState absorbed)`;
- flatten(readParts absorbed 2) with `advanceA params (decodeState absorbed)`.

Use the same source record, tag=160+j, decoded state and H throughout. A finite caller-specific Digest32 law must connect each successful result to H at its exact address; no production-SHA ideality or foreign axiom is manufactured. To match completion, also prove `(T a).getD(acc a)=decodeState block` for each actual read1 address a; if acc=H and T is the compatible actual read table, derive it from that table construction. Arbitrary T/acc do not imply source challenge equality. Merely reusing a table from a different run is insufficient.

The separate `htyped/ha` link must identify the decoder's recovered rs with this source-constructed record list at the actual already-read target address, using the same init/c1/state/endpoint and carried read2 states. Existing `RawRoundCompletion.decode_records`, carried-last variant, `TypedPrefixExtension` and `SemanticPrefixCutAgreement` can transport a checked trace; none supplies the missing source trace/table relation by itself.

## C1 auxiliary word and selected typed context are also open

The source Prefix parser returns a32-byte C1 root, not a literal `C1Word`. Successful `public_transcript` supplies the exact serialized public input and the digest-initialization call on that same root; C's `PreparationBinding.helper_binding` addresses public-wire parsing only. It does not construct a C1 word, establish commitment openings, or identify an auxiliary word with a recovered full-log word. The row0 empty-record equality similarly erases C1 auxiliary metadata and cannot prove its custody.

The existing accepted **representation** results are precise: `LiteralSemanticCodecBridge.row_zero_record_of_decode` fixes the row0 raw record; `LiteralTypedContext.context` constructs a typed context from already supplied decoded C1 plus publicBase and extraClaims; `LiteralTypedContext.c2Words_full`/`c2Base_full` and `LiteralSemanticPayloadBridge.pair_c2Words`/`pair_c2Base` identify lanes once the same C1/C2 words are supplied. `RawCutConstructedWords.initial_root` and `buildWords_eq_full_from_messages` recover commitment targets/full maps from the strict literal-message constructors and a no-hit recorded run. Their own scope says actual verifier acceptance must still imply those message/parser facts. None is an accepted theorem that current Rust Prefix success produces the literal `.initial root c1Word` or that caller metadata equals the recovered C1 word.

Therefore the matched literal-context path additionally needs: the actual row0 `.initial` constructor with exactly the source C1 root and a justified C1 word; `LiteralTranscript.c1At` success on the same prefix; the fixed public mapping/publicBase proof; equality of the context C1 to the accepted full-log recovery map; and the intended extraClaims source (or a documented classifier-specific zero erasure). Preserve the distinction between the C1-only context's intentional zeroC2 lanes and the actual C2 semantic message: `c2Words_full` restores the supplied C2 lanes but does not create their custody. A model reader may succeed for arbitrary auxiliary C1/C2 values while the actual source-to-context claim remains unproved.

The Digest32/address law above must also cover the actual **initialization** call used to establish the starting selected state/public/C1 binding, not just each row's read1/read2 calls. Only after those source/context/table identifications can a generic completed-read success be reported as the requested actual selected `hread`, and then as the semantic classifier's actual input.

## C2 constructor and custody remain separate

The actual row2 parser proves a typed `.c2Root root` from the32 root bytes. It cannot recover a `LiteralTranscript.C2Word` from that root. The generic `SelectedSemanticPrefix.read recoverC2` only uses the chosen callback in `SemanticPayloadView.toMessage`; therefore callback existence is not custody and is not a runtime extraction result.

For the literal path, separately supply the actual `.c2 frame word` constructor at logical row2, strict `LiteralTranscript.valid`, byte equality to that same parsed frame, and custody of `word` (existing `LiteralSemanticPayloadBridge.CarriesC2`). Then `LiteralSemanticPrefix.c2Pair` and checked `callback_toMessage`/`read_of_payloads` supply the exact `.base (.h1 … …)` interpretation. This witness must not be inferred from root bytes, a later table, or B's readonly projection premise. The row0 `.initial`, row2 `.c2`, other semantic `.payload`, and ordinary-challenge constructor schedule also remains explicit for literal read success.

## Current status

Checked: actual Prefix typedFull, actual begin15 ordered calls/bytes/rank/carry, current QM31 nominal transport, helper serializer success/binding, and first caller's actual decoder/selector prefix. Current tx1_finish caller model and success inversion have now been checked with only standard Lean axioms; its named verify/query boundaries remain explicit. Missing: actual verify caller reachability to public_transcript and ordered rows15–24; actual recovered-log hbytes; matching Digest32/table/typed-address provenance; literal constructor/C1/C2 context and custody; actual row25/26 and opening/query completion for all33. No full25 hread or complete source acceptance claim follows yet.
