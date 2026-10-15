# J1 literal-protocol code contract (source inventory)

This note records the current Lean definitions and theorem boundaries inspected for the literal-word protocol model. It is a code inventory, not a claim that J1 is closed. Repository base at inspection: `f525df3ca612d245188094adb102c99533cc74fc`.

## Literal word and transcript representation

`MixedLeafEncoding.C1Slot` is `(Fin 26 → M31Exact) × QM31Exact`; `C2Slot` is `Fin 2 → QM31Exact` ([`MixedLeafEncoding.lean`](../lean/MixedLeafEncoding.lean), lines 13–16). `LiteralTypedWords.C1Word` and `C2Word` each index these slots by `Fin 1048576`. Its `word` maps the 26 base lanes to the C1 M31 coordinates, lanes 26 and 27 to C2 QM31 coordinates 0 and 1, and lane 28 to the C1 QM31 coordinate ([`LiteralTypedWords.lean`](../lean/LiteralTypedWords.lean), lines 16–36). `word_typed` states the mapped lanes lie in their selected subfields. `word_recovered_eq` identifies this literal view with the existing `TypedRecoveredWords.word` when given its packed projections, and `word_eq_zeroC2Word_outside_c2` says changing C2 does not change lanes other than 26 and 27. These are representation equalities; they do not prove a decoded transcript contains those words.

`LiteralTranscript.Message` has constructors `initial root word`, `payload bytes`, `c2 bytes word`, and `second bytes word`; `erase` keeps the initial root and byte payloads while erasing the attached words ([`LiteralTranscript.lean`](../lean/LiteralTranscript.lean), lines 24–42). Its `valid` schedule permits initial at row 0, C2 at row 2, second at row 30, and ordinary payload messages at the other rows below 33 (lines 44–50). The optional list accessors `c1At`, `c2At`, and `vAt` read exactly indices 0, 2, and 30, respectively; their append-stability results require the corresponding index to be already present (lines 52–90). These are list-index facts, not commitment-to-word recovery results.

`LiteralTranscript.samp` erases a literal prefix/message and calls `UnifiedSampler.samp` for the selected parameters (lines 67–71). `LiteralRun.erase_transcript` equates the literal recursive run after erasure with a directly run erased transcript. `LiteralProtocol.transcript_eq` imports that run and equates the protocol transcript to it ([`LiteralRun.lean`](../lean/LiteralRun.lean), `erase_transcript`; [`LiteralProtocol.lean`](../lean/LiteralProtocol.lean), lines 39–56). This establishes the model's sampler projection only.

## Semantic-prefix reader

`LiteralSemanticPrefix.parseMessage` accepts a message only when `LiteralTranscript.valid` holds. An initial message maps to `.base .none`; ordinary payload and C2 byte payloads pass through `SemanticRecordCodec.decode`; the C2 branch supplies the callback extracted from that literal C2 word; the second-word constructor is rejected in this 25-row reader ([`LiteralSemanticPrefix.lean`](../lean/LiteralSemanticPrefix.lean), lines 31–44). `read` accepts only `.ordinary` challenges and offsets less than 25, recursively returning parsed semantic messages paired with the ordinary challenge value (lines 46–57). The proved `read_length` and `read_append` are structural results about this reader; the evidence bundle is [`lean-literal-semantic-prefix-20261015`](../evidence/lean-literal-semantic-prefix-20261015).

Separately, `SelectedSemanticRead.read` sequences strict `SemanticRecordCodec.decode` results over a typed 25-row list of `RawRec` values; it proves the pointwise read characterization and stability after appending a suffix once `24 < rs.length` ([`SelectedSemanticRead.lean`](../lean/SelectedSemanticRead.lean)). `SelectedSemanticMessages` supplies typed payload encodings and codec round-trips. `SemanticPayloadView` turns each typed payload into an old `SemMsgZ` value using an explicit C2-recovery callback; `SemanticPayloadView.rounds` constructs the old 25-pair list, with proved accessors for C2 root at row 2, mask sum at row 14, and coefficients at rows 15–24. Those payload/list mappings do not themselves establish accepted-run or Rust parser correspondence.

## Protocol relation and generic FS2 obligations

`LiteralProtocol.Decoder` is an explicit parameter from an address and oracle table to an optional sampler for a prefix/message/challenge triple; `protocol` sets 33 rounds, uses the literal sampler, and stores this supplied decoder ([`LiteralProtocol.lean`](../lean/LiteralProtocol.lean), lines 18–37). The relation is `∃ p, SemanticPublicWire.parsePublic pub.pubBytes = some p ∧ SpendRelation.Rspend p w`. The `Witness` and `Rspend` relation are defined in [`SpendRelation.lean`](../lean/SpendRelation.lean): the relation includes canonical public shape, input-note membership, bounded input/output/change values and conservation, change commitment, variant output, and append binding. This records the relation the protocol selector targets; it is not proof that an accepted proof yields a witness.

The `extract` field in `LiteralProtocol.protocol` is `GenericNoHit.chooseWitness relation pub`, a classical specification-level selector independent of the supplied table. The proved `d1` applies `GenericNoHitFS2.d1`; `extracted_relation` says a returned selected witness satisfies the relation (lines 29–37, 58–67). This is the selector-based D1 bookkeeping only. `GenericNoHitFS2.d2` still takes the fixed-prefix density bound `hdensity` as a premise (lines 50–64). `GenericNoHitFS2.d3` still takes the terminal accepted/no-hit implication `hterminal` as a premise (lines 66–89). The generic module therefore does not prove the selected density or terminal claim.

No source-to-Lean accepted-transcript refinement, INJ result, decoder-closure theorem, terminal acceptance-to-witness theorem, completed knowledge extractor, or privacy/release conclusion is recorded here.

## Source pins

The following SHA-256 values pin the exact files inspected in this worktree:

- `docs/research/100bit-spend-path-20261013/lean/LiteralProtocol.lean` — `14d0a78e946685ba0abf318aff1e20e6f465eb3d0fa2fadb1f4655aee75e921f`
- `docs/research/100bit-spend-path-20261013/lean/LiteralTranscript.lean` — `2b76b95f5dffb2856f1af3884859d3d8d16e60bf47c0950559fe3c5e44ec4ed6`
- `docs/research/100bit-spend-path-20261013/lean/LiteralTypedWords.lean` — `76dea224a230a9974969d92289582bf39ee1da74734d47a966aafc5f8b98569c`
- `docs/research/100bit-spend-path-20261013/lean/MixedLeafEncoding.lean` — `775cd8c85f1920cefa73066a1fc7f56a34d1350bd3cb769b59f9132b9494a951`
- `docs/research/100bit-spend-path-20261013/lean/LiteralRun.lean` — `c554a1cf8d1f94da060331b9d3bf96675666701be3a7437297a27460a3a1bf12`
- `docs/research/100bit-spend-path-20261013/lean/LiteralSemanticPrefix.lean` — `73a42746feb451314c805bdd1ed5df46c1ae231acbf7a02efac77012c349877f`
- `docs/research/100bit-spend-path-20261013/lean/SemanticPayloadView.lean` — `63d8ee366a6ca1beb5c4de26110419ddcaf83f87efb8de9d3151e24c0ef6506b`
- `docs/research/100bit-spend-path-20261013/lean/SelectedSemanticRead.lean` — `ac332f97ddbcb98feaf6d4df30f54995fcec4e430ccb374f07d1afafc1d0eb59`
- `docs/research/100bit-spend-path-20261013/lean/SelectedSemanticMessages.lean` — `c3664c130913f29caed63a89326d9d37b3b2bf7f7e838e68da6db23ae3ac550c`
- `docs/research/100bit-spend-path-20261013/lean/SelectedSemanticPrefixFacts.lean` — `733444507012726a2d29b8b087f6c21f37ba4a96bb94aef87f51e7776d21004b`
- `docs/research/100bit-spend-path-20261013/lean/GenericNoHitFS2.lean` — `5f5a904a6d1d885f2cc442bdd5177714f0ef2de5147a75b395516ad219e6534a`
- `docs/research/100bit-spend-path-20261013/lean/SpendRelation.lean` — `d2546e86976424b968a3d3fa546c1d9b9da44bf405eea19ea8bb053f37052e8e`
