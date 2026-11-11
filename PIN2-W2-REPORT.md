# PIN2 W2: Lean mirror of the public-input binding suffix

Worker W2, branch `fix/pin2-lean-20261110` (from research `f168fce2119`), worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. Evidence directory: `docs/research/100bit-spend-path-20261013/evidence/pin2-public-binding-20261110/`. Compile log: `PIN2-W2-COMPILE.tsv` (35 focused compiles). Impact table: `PIN2-W2-IMPACT.tsv`. Nothing was pushed and nothing ran on the build host.

## 1. Which copies are the release copies

The local L187 closure has no `l187_plan.json`, so I identified the release sources another way. I read the import list of every one of the 14,101 closure objects with a small `readModuleData` program (`impact-scan/Imports.lean`). Then I compared each candidate source on `research` against its closure object. `R1SemanticPublicWire`, `R1SemanticPublicWireRoundTrip`, `R1SemanticPublicWireInjective` and `R1SemanticPublicByteBinding` have closure objects that are byte-identical to the objects committed beside one evidence copy, so those sources are certain. The other modules each have exactly one distinct source blob on `research`. The one exception is `PublicCodecAgreement`, which has two. The closure object holds `encode_none_iff` and imports `R1PublicByteCodecLaws`, `R1SemanticPublicByteBinding` and `R1SemanticPublicWireSurjective`, and that matches only `docs/research/100bit-spend-path-20261013/lean/PublicCodecAgreement.lean`. `R0P.Public` printed from the closure object has exactly the 11 fields of the single `R0P/Core.lean` blob. The path and git blob of every module are recorded in `release-originals/PROVENANCE.tsv` and `first-layer/PROVENANCE.tsv`, and each untouched original is kept in `release-originals/`.

One oddity in the release closure. `R1PublicCodecAgreement` (blob `216684c1`) and `PublicCodecAgreement` declare the same constants in the same namespace (`AspisR1.PublicCodecAgreement.u64_emit_eq_index_encode`, `encode_toPublic_eq_wire_encode`), and `ExtractedPublicCheckedBridge432` imports both. I changed both copies identically (each gains `toPublic_wireOK`). The duplication should be reviewed, but it is not caused by PIN2.

## 2. The new model

`R0P.Public` keeps all 11 fields with their names and gains three after `nextFrontier`: `pool : List (Fin 256)`, `deploymentDomain : List (Fin 256)` and `destination : Option (List (Fin 256))`. The lengths are not part of the type; `PublicOptionShape.canonical` imposes them. The 15 compiled modules show no residual family or other `R0P.*` module building or destructuring `R0P.Public`: ten unchanged first-layer `R0P` modules rebuilt against the new structure without edits.

The wire carrier `SemanticPublicWire.Common` gains `pool deploymentDomain : Bytes32` and `destination : Option Bytes32`, where `Bytes32 := {l : List Byte // l.length = 32}`. `Wire` keeps its two constructors unchanged. The parser reads the appended suffix in the order fixed in the plan, before the trailing-byte check:

```lean
def readBytes32 := PublicByteCursor.read 32 decodeBytes32
def readDestination : List Byte → Option (Option Bytes32 × List Byte)
  | [] => none
  | tag :: rest =>
      if tag = 0 then some (none, rest)
      else if tag = 1 then (readBytes32 rest).map (fun p => (some p.1, p.2))
      else none
def decodeAfter ... := do
  let (index, rest) ← readIndex bytes
  let (snapshot, rest) ← readFrontier rest
  let (root, rest) ← readDigest rest
  let (frontier, rest) ← readFrontier rest
  let (pool, rest) ← readBytes32 rest
  let (domain, rest) ← readBytes32 rest
  let (destination, rest) ← readDestination rest
  if rest.isEmpty then some ⟨..., pool, domain, destination⟩ else none
```

`PublicOptionShape.canonical` now requires `destination = none` for a private transfer and `destination.isSome` for a withdrawal. Both variants also need `bindingLengths`: pool and domain each 32 bytes, and any destination 32 bytes. `check` is the matching Boolean, and `check_eq_true_iff` is re-proved. The statements of `private_transfer_shape` and `withdrawal_shape` are unchanged, and there are new lemmas `private_transfer_destination`, `withdrawal_destination` and `canonical_bindingLengths`. The two `*_updated_canonical` lemmas are statement changes: they now take the length hypotheses, and the withdrawal form takes the new destination.

Lengths: a canonical transfer is 1,520 bytes (was 1,455) and a canonical withdrawal is 1,524 (was 1,427). The longer variant is now the withdrawal. `encode_length` for an arbitrary wire is 1519 (transfer) or 1491 (withdrawal), plus 1 or 33 for the destination field. The transcript initialisation frame (75 + public bytes) becomes 1,595 or 1,599 (was 1,530 or 1,502). `SelectedTranscriptParams.L = 131072` is unaffected.

Every module was re-proved and compiled against its new predecessors only, which makes the codec layer coherent:

- **Exact statements kept:** `parsePublic_canonical`, `toPublic_index_bound`, `decode_encode`, `parsePublic_encode`, `decodeAfter_sound`, `encode_of_decode`, `toPublic_injective`, `exists_wire`, `parsed_wire`, `parsed_exact_bytes`, `bytes_unique`, `existsUnique_bytes`, `parse_exists_iff`, `parsePublic_eq_some_iff`, `decode_eq_parsePublic`, `parsePublic_of_decode` and `encode_toPublic_eq_wire_encode`. The last is the agreement between the compositional codec and the wire model.
- **Statements changed, constants only:** `encode_length`, `parsed_length`, `parsed_length_bound` (now ≤ 1524), `parsed_init_fits` (≤ 1599) and `parsed_init_frame_length` (1595/1599).
- **Statements changed, guard:** `encode_none_iff` and `encode_exists_iff` now refer to `WireOK` (index bound plus 32-byte lengths) instead of the index bound alone.

The compositional codec `PublicByteCodec` gains three `Fields` components (`Bytes32 × Bytes32 × Option Bytes32`) and `bytes32_lawful`. Its encoder accepts exactly the `WireOK` records.

`PIN2_PublicWireTeeth.lean` proves the rejections, so the change has teeth beyond prose:

- the old 1,455/1,427-byte lengths never parse;
- a transfer that carries a destination is rejected;
- a withdrawal without one is rejected;
- a `has_destination` byte other than 0 or 1 is rejected;
- trailing bytes after a complete encoding are rejected.

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` throughout; there is no sorry, axiom, `native_decide` or raised heartbeat limit. Peak RSS was 2.8 to 2.9 GB for every compile and the longest wall time was 22 s.

## 3. First downstream layer

23 modules in the release closure import one of the 13 changed codec modules directly. I compiled the 14 whose other imports do not depend on `R0P.Core`, so those results are coherent rather than a mix of stale objects:

- **Ten `R0P` modules and two others, unchanged source, all exit 0 against the new `R0P.Core`:** `R0P.Value`, `Asset`, `CopyConstants`, `CoreExt`, `EmptyRoots`, `Occupancy`, `Path`, `PoseidonConstants`, `Positive`, `Positivity`, plus `PublicPrimitiveDecoderWork` and `R1TraceValueDecode`.
- **`R1PublicSourceRaw` and `R1PublicSourceRawMap` (the handwritten source-facing serializer model) needed edits, and I made them.** This turned up a real obligation. The raw source `Public` does not force "destination present iff withdrawal", so `mapPublic_canonical`, `mapped_canonical` and `decode_of_serialize` now take a new premise `DestinationShape p`. That premise sits alongside the existing `NonzeroWithdrawal` and is a statement change. It must be discharged from the Rust constructors, where `private_public` sets `None` and `withdrawal_public` sets `Some`, once W1's source exists.

I stopped at this layer. The other nine first-layer modules each import many modules that themselves depend on `R0P.Core`, so compiling them would need those rebuilt first. Two of the nine need source edits: `R1SelectedTranscriptParams` (the `initFits` bound) and `ExtractedAdapterStageBindingObligations.parsePublic_of_wire_decode` (it unfolds parser internals). The other seven need only a rebuild: `SpendRelation`, `ExtractedDecoderPublicBinding`, `ExtractedPublicCheckedBridge432`, `LiteralTerminalCandidate`, `R1LiteralTerminalSpend`, `RawCutWordsFromRunPublicValid` and its `Bin` twin. `SpendRelation`, for example, needs 36 such intermediate objects.

## 4. Impact walk

Method: three kernel-level scans over every object of the release closure (`impact-scan/`). For every constant they record the watched constants used in its type and in its value, theorem bodies included. They also record whether its type or value contains one of the length literals (1455, 1427, 1530, 1502 and neighbours, 815, 1320). The literal hits were filtered by hand: prime certificates, R17 power tables, query-scan rows and the interpolation budgets contain the same numbers by coincidence. This is a reference walk, not a guess, but it is kernel-level. It cannot see a tactic proof whose kernel term avoids the watched names and still breaks on a field addition, so the classifications below are a lower bound for "needs an edit".

Rebuild cost: 10,585 of the 14,101 closure modules import `R0P.Core` transitively, and 565 of the 599 ledger rows have owner modules among them. Any PIN2 change therefore means a new coherent cold replay (claim-draft gate 8), even though the source changes are local.

Outside the 15 modules already done here, these declarations need edits (the full list is `PIN2-W2-IMPACT.tsv`):

| Group | Modules | Declarations | Kind |
| --- | --- | --- | --- |
| (b) Maps over `R0P.Public` that rebuild it field by field: `SpendDataMap.mapPublic` (+`_comp`, `_id`), `AppendBindingMap.map_outputPair`, `PublicBaseMap.mapPublic_base`, `SpendRelationMap.canonical_map_iff` / `variantOutput_map_iff`, `DigestFamilyFieldTransport.map_keys` / `map_target`, `NKR_DigestAssociation.keys`, `NKR_DigestOptionalValue.carry` / `recipient` | 7 | 12 | mechanical (copy the three byte fields) |
| (b) Builders of `R0P.Public` from the extracted Rust public: `FIw_PublicModel.ofPublic`, `FJq_PublicModel.common` / `model` / `mapped`, `FJn_ModelInputs.index` / `variant`, `FIz_*` family `value` / `read` / `next` | 9 | 12 | mechanical after Stream C re-extracts `SemanticPublic` with `destination` |
| (a, c) Parser-work and allocation models that restate `decodeAfter` with counters: `PublicParserWork` (`decodeAfter`, `*_value`, `*_work`, `expect`, `parsePublic_value`), `PublicParserAllocationM10.decodeAfter`, `PublicParsedIndexM10.bound` | 3 | 10 | needs thought: three more reads change the work counts, and the M10 extractor-cost budgets downstream must be checked |
| (c) Consumers of the source-model theorems that now take `DestinationShape`: `PublicSourceBoundary.parseRaw_of_source_success`, `PublicSourceRawSuccess.*`, `ExtractedPublicCheckedBridge432`, `ExtractedAdapterStageBindingObligations.parsePublic_of_wire_decode` | 4 | 5 | needs thought: discharge `DestinationShape` from the extracted constructors |
| (a) Serializer length and offset theorems on the extracted `public_bytes`: `NHG_Lengths.{source,bound,returned,prefix_room,digest_domain}`, `NHG_ProducerDomains.{frontier_room,words_room}`, `NHG_ProducerWidths.field_domain`, `NHG_PublicCarrier.{begin_carrier,same_execution}` | 4 | 10 | needs thought: re-prove against the new body, 1455/1427 → 1520/1524 (the 815 offset of the next frontier is unchanged) |
| (a) Transcript-record sizes: `WireBindingRecordCodec.Tx1Class.size` (`initTransfer` 1530 → 1595, `initWithdrawal` 1502 → 1599), `tx1_class_safe`, `SelectedTranscriptParams.publicStatement`, `F3J_Public.from_cut`, `F3V_Public.from_decode` | 4 | 5 | mechanical, except that `tx1_class_safe` must be re-checked against its size bound |
| (a) Fixture and recorded-run evidence on the concrete 10 November bytes: `NDO_JFp_*` (InitBytes, SHADigest, SeedHash), `NDO_JFs_*` (five serialization theorems), `NDO_JFu_{OracleSeed,TranscriptLength}`, `NDO_JFw_{NativeRow18,Records}`, `NDO_JFz_{Parsed,Row17,Row18}` | 15 | 22 | needs regeneration from the new devnet fixtures (they fix 1455 seed bytes, a 1530-byte init record and the row-18 header at offset 1530) |

Totals outside this branch: 76 declarations in 46 modules. 29 are mechanical: 12 in the first row, 12 more once Stream C has re-extracted, and 5 for the record sizes, with `tx1_class_safe` to confirm. 47 need thought or regeneration: 10 cost-model, 5 premise discharge, 10 serializer and 22 fixture. These are source-level owners; equation lemmas generated in other modules are counted with their owner. Another 29 declarations in 14 modules (including `SpendRelation.Rspend`, `check`, the `*SpendExtraction` and `*WitnessExtract` theorems, and `rspend_map_iff`) use `canonical` or `check` inside proofs but do not unfold the parser. I expect them to need only a rebuild unless a proof destructures `canonical` by position.

Done in this branch: about 50 changed and 40 new declarations in 15 modules. That is a text-diff count and over-counts a few declarations next to inserted doc comments.

Group (d), the relation and the extractor's public decoding: `SpendRelation.Rspend`, `LiteralProtocol.relation`, `RawRecordedPublicSpendExtractor*` / `*Bin` (`extract`, `returned_relation`, `extract_eq_of_public_parse`), `RawCutWordsFromRunPublicValid*.runDecodedPublic` and `GSByteJointSpendExtractor*` all use `parsePublic` and `canonical` only as functions. None constructs or destructures `R0P.Public` or unfolds the parser, so all of them need only a rebuild. Their meaning does change: `Rspend` now also requires the destination and length shape. `Rspend` does not, and could not, say that the destination equals the account the funds actually reach. That fact, which is the purpose of Finding 20, holds only if the verifier program builds `public_bytes` from the real instruction accounts. It is a W1 and adapter-row obligation, not a Lean codec fact.

Extracted Rust (Stream C): 585 declarations in 302 modules refer to the Aeneas-extracted `SemanticPublic`, `r0.Public` or `F3_Model.SemanticPublic`. 62 of them, in 30 modules (three of them `RPu_FIq_*` native-extraction modules), use the constructor or eliminator of the extracted struct (`F3_Model`, `NHG_Semantic.{transferValue,withdrawalValue}`, `NKR_TermPublic`, the `F3T_ByteCarrier.input` family, `Rc4_Model`, `ExtractedPreparationSerializerWhole` and others). They break when the struct gains `destination` and need mechanical edits after re-extraction. The withdrawn `ReviewedTranscription-PublicPreparation.public_bytes` evidence (`NPL_PublicBytes.gate_total_length`, 1455/1427, outside the L187 closure) must be redone against the new body.

Ledger rows (`docs/r1/LEDGER-599.md` on main, from `evidence/ledger30-20261111/NNN_LEDGER.json.xz`):

- **Bodies change under W1:** TX1:254 `r0::Public::public_bytes`, TX1:249 `private_public` and TX1:266 `withdrawal_public`. TX1:252 and TX1:253 (`public_bytes::fields` / `frontier`) belong to the same function's owner set; their bodies are probably unchanged, which the body-SHA gate will show.
- **Owner modules need edits:** TX1:131 `r1_semantic::public_transcript` (owners `NHG_Lengths`, `NHG_PublicCarrier`) and TX1:150 `r1_wire::begin` (`NHG_PublicCarrier`).
- **Owner modules break on the extracted struct change:** TX1:228, 237, 239, 255, 256, 260, 261, 263 and 264 (owner modules `NJL_OccupancyParent`, `NLH_CompRoot`, `NHG_SnapshotViews`, `NHG_Semantic`, `NLH_WrapperRoot`, `NKI_InitialRoot`, `NLH_SemanticFold`, `NLH_PartsRoot`, `NIH_TransitionWords`).

That is 16 rows with a source or edit impact (`impact-scan/ledger_impact.json`). No TX2 row was flagged. The remaining 565 rows need only a coherent rebuild and replay.

Claim-draft items affected (`design/SOUNDNESS-CLAIM-DRAFT-20261108.md`):

- finding 20, which this work implements on the Lean side;
- 4.7a, the withdrawn public_bytes transcription row, whose evidence must be redone;
- gate 7, extraction provenance for the re-extracted modules;
- gate 8, the L187 replay, which this change invalidates;
- gate 9, the L188 ELF association, which needs a new ELF;
- gate 14, the frozen pins, which move;
- gate 4, the statement audit: the printed text is unchanged but the meaning is changed (below).

## 5. Top-level statements

I printed `AspisR1.TAS_FinalB.deployed_splitB` and `deployed_charge` from the release closure (`impact-scan/Top.lean`, `Top.out`). Their statements name 39 and 73 constants, none of which is a declaration changed here, so neither printed statement changes textually. Following the definitions, not the proofs, from those constants reaches 25 changed declarations: `R0P.Public` and its projections and `mk`, `SemanticPublicWire.parsePublic`, `Wire`, `Common`, `toPublic`, `expect`, and `PublicOptionShape.canonical` / `check`. So the theorems' meaning changes as intended, because the parsed statement now binds the suffix, while their text does not. The constants in `deployed_charge`, such as `fx.Q0 + fx.Q1 + 2965` and `F3T_Numeric.total`, are query counts and do not depend on public-byte length, because the initialisation frame is a single oracle record. The record-size bound `tx1_class_safe` still has to be confirmed. This rests on the definition walk and on the printed text; I did not recompile either theorem under the change.

## 6. What the next worker must do

1. Take W1's Rust and have Stream C re-extract the changed functions and the `SemanticPublic` type. Then fix the 62 extracted-struct constructor sites and the nine builder modules of group (b) mechanically.
2. Prove `DestinationShape` for the extracted `private_public` and `withdrawal_public`, and thread it through the four source-boundary consumers.
3. Re-prove the `NHG_*` serializer length and offset theorems on the new `public_bytes` body. Update `WireBindingRecordCodec` and the three transcript-size users, and re-check `tx1_class_safe`.
4. Redo `PublicParserWork` and `PublicParserAllocationM10` with the three extra reads, and check every M10 cost budget that consumes their work counts.
5. Regenerate the `NDO_JF*` fixture theorems from the PIN2 devnet run.
6. Overlay order: start from `l187-closure/overlay-PIN2`, which holds the 13 codec objects, the teeth module, the 12 unchanged first-layer rebuilds and the two source-model edits, all compiled coherently. Rebuild the remaining dependents in import order on the build host under capped scopes. Then run one coherent cold replay of the 14,101-module closure, one axioms audit of the two top theorems, and the ledger gate.

Target not yet established.
