# External J1.R4 integration review

Review is read-only. Compared commits `64bbb8fc2e66f99f13c28f2ed6fc6ed701a59db0` and `95bf664bcd5e1cf945d0be561aca2492321e9c05` (branch `codex/r1-j1-r4-review-20261015`) with root HEAD `f1edebd66d8ea21178b8f4f34b4c623fc3934413` in the same worktree. The external branch descends from `136b746805f3438507732622c9b4e50f36bf49f9`, which is also the merge base. A three-way merge inspection with `git merge-tree --write-tree f1edebd66d8ea21178b8f4f34b4c623fc3934413 codex/r1-j1-r4-review-20261015` produced tree `bf7442e4bd93eca02f9dd462cf75e754c37bd4f5` with no conflict markers. Relative to the merge base, the branch adds 170 paths and modifies 3 paths; it deletes no paths. The earlier two-tree diff against root HEAD showed inherited root-only additions as deletions, which was not evidence of three-way merge deletions. This review does not decide whether to merge.

## Axioms and assumptions

The seven added source files contain no `sorry`, `admit`, or custom `axiom` declarations. The checked manifests record standard Lean axiom sets only: `propext`, `Classical.choice`, and `Quot.sound` for the public projection/codec laws and semantic prefix codec; the generic typed-prefix parser reports `propext` and `Quot.sound`. `PublicByteCodec` itself has no public audit entries in its manifest. This is a source/evidence inspection; no compilation was run here.

No theorem statement reviewed weakens its own premises relative to its stated result. In particular, the extractor theorem retains `PublicBase`, canonical option shape, `BaseTyped`, `ProductionHolds`, and `CopyLinkBalance`; it does not claim extraction from an arbitrary public/trace pair.

## Seven added modules and root-side overlap

| External module | Main API / role | Relationship to root HEAD |
|---|---|---|
| `PublicBaseProjection.lean` | Projection `Public WideExact → Public M31Exact`; `PublicBase` range facts, project/embed round trips, canonical-option preservation, and `rspend_project` / `spendCheck_project`. | Extends root's generic `PublicBaseMap.mapPublic_base` with projection-specific inverse and spend-check facts. These are compatible in shape but use the fixed `ExactBaseProjection.embed/project`; avoid duplicating generic range lemmas. |
| `PublicByteCodec.lean` | Compositional prefix codecs for section-9 `R0P.Public M31Exact`; strict `parseRaw`/`decode`, U32/U64, M31/digest/frontier fields and options. | Strong overlap with root's `SemanticPublicWire` (`Wire`, `encode`, `decode`, `parsePublic`) and `PublicByteCursor`, field-block/index codecs. Both describe the same transfer/withdrawal public byte order. External codec is a `PrefixCodec` over `Public` and exposes a reusable lawful-combinator API; root codec uses a variant-indexed `Wire` plus `toPublic`. Compare/relate encoders before keeping two canonical models. |
| `PublicByteCodecLaws.lean` | Generic lawful-combinator proofs and exact encode/decode, strict trailing/truncation/bad-tag rejection, zero-withdrawal rejection and encoding uniqueness. | Root already has `SemanticPublicWireSound`, `SemanticPublicWireRoundTrip`, injectivity and `PublicByteCursor.read_sound`; those facts cover its variant-indexed model. External lemmas may be reusable for prefix combinators, but are not a drop-in theorem for root's `Wire` without a representation equivalence. |
| `PublicByteCodecLengths.lean` | Symbolic length results; canonical transfer 1455 bytes, withdrawal 1427 bytes. | Root's semantic wire layout docs/source inventory already have these sizes; check root `SemanticPublicWireRoundTrip.encode_length` before duplicating. External theorem directly speaks about `PublicByteCodec.encode` and `R0P.Public`. |
| `PublicTraceWitness.lean` | `extract_complete_of_typed_public` lifts `TraceWitnessExtract.complete_of_production` through public projection. | New bridge complementary to root's literal-word route, not an oracle/byte parser. Its explicit premises remain `hpub`, `hshape`, `hbase`, and `ProductionHolds ∧ CopyLinkBalance`. It is not a complete J1 extractor absent those facts and a path from actual public parsing/trace to them. |
| `SemanticPrefixCodec.lean` | Dependent `Full := (i : Fin 25) → RowPayload i`, `decodeOne/decodeFrom`, strict 25-row full parser, encode/decode round trips, prefix stability/failure persistence. Input is `List Bytes` of already-delimited records. | Root has `SemanticRecordCodec` for individual row payloads plus `SelectedSemanticPrefix.read` / `read_append` over selected literal messages and `TypedPrefixExtension` over recovered `RawRec` lists. External generic full-vector codec is a useful adapter not currently the same interface; it does not split a byte stream, consume challenges, bind a table, or establish source correspondence. |
| `TypedPrefixParser.lean` | Generic dependent row parser over already-delimited `List Raw`, with append, length, decoded-row, prefix-stability and failure-persistence results. | Root's `TypedPrefixExtension` transports the existing raw-record recovery parser across trace extension; it is not the same generic dependent `Sigma Payload` API. Potential low-level reuse, but distinct input/output representations. |

Root-side exact declarations inspected include `AspisR1.PublicBaseMap.mapPublic_base`; `AspisR1.SemanticPublicWire.encode/decode/parsePublic`; `AspisR1.SemanticPublicWireSound.encode_of_decode`; `AspisR1.SemanticPublicWireRoundTrip.decode_encode/encode_length`; `AspisR1.PublicByteCursor.read/read_sound`; `AspisR1.SemanticRecordCodec.RowPayload/encode/decode`; `AspisR1.TypedPrefixExtension.semantic_typed_append_eq/opening_typed_append_eq`; `AspisR1.SelectedSemanticPrefix.read/read_length/read_append`; and `AspisR1.LiteralTranscript` / `AspisR1.LiteralSemanticPrefix` for the separate literal-word parser route.

## Evidence details

External green source hashes and object hashes are recorded in the commit's package manifests:

- `PublicBaseProjection`: source `f685df74…a9ccdc25`, object `d283ceba…991e0989`.
- `PublicTraceWitness`: source `9d1fa2fd…1555aa97`, object `7709bb10…7219397`.
- `PublicByteCodec`: source `74ee599f…7d239e5b`, object `409de20b…11bbf6d1`.
- `PublicByteCodecLaws`: source `4b3a9824…0a1d516a`, object `60376c25…1214b42ce`.
- `PublicByteCodecLengths`: source `9452990a…bcb5766d`, object `630fdce3…6751c80b`.
- `SemanticPrefixCodec`: source `c00e923e…426dcbfd`, object `dfe107ab…565451c`.
- `TypedPrefixParser`: source `bafe29f6…f097a5ef`, object `6bb4127e…6750284`.

The manifests preserve failed attempts where present and identify the green attempt. The public base package records projection attempt `a` and trace witness attempts `a/b` failed, `c` green. The public byte codec package records codec `a` green and laws `a/b` failed, `c` green. Lengths `a` failed, `b` green. Semantic prefix `a/b/c` failed, `d` green. Typed parser `a/b` failed, `c/d` green. These attempt records are from the branch evidence; no replays were made for this review.

Commit `64bbb8f` repairs the older semantic-payload-view evidence bundle's direct-import source pins. It records source snapshots for `R1SemanticRecordCodec` (SHA `5cf8fb65…229bcbd3`) and `R0P.MaskView` (SHA `f2719883…3a8b44b`), and explicitly labels the repair retrospective: `replay_performed: false`, `historical_compile_time_import_source_attestation: false`. That is honest metadata repair, not newly established compile-time provenance. Root HEAD contains a separate current pinned replay bundle; preserve the distinction between the repaired historical package and that replay.

## Integration cautions

1. The external branch's root-relative diff includes deletion of current root's public codec, selected parser, literal protocol, and other evidence files because it is based on the earlier `136b746` state. Accepting either commit must not bring those deletions over root HEAD.
2. `PublicByteCodec` and root `SemanticPublicWire` overlap on the exact public layout but differ in carrier/API (`Public M31` plus `PrefixCodec` versus `Wire` constructors plus cursor decoders). They need an explicit equivalence if both remain in the integrated tree.
3. `SemanticPrefixCodec` assumes records have already been split into a list. It does not substitute for root's current strict literal-message/table recovery, and its full 25-row result is a different codomain from the selected readers.
4. None of these files supplies Rust parser correspondence, ASF8 binding, current verifier acceptance, source-trace extraction without the explicit trace premises, later opening decoding, or the missing selected literal C2 callback. No such closure is inferred here.
