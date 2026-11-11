# PIN2 W3b: serializer lengths, transcript record sizes, parser work and M10 budgets

Worker W3b, branch `fix/pin2-lean-20261110` (from W2 at `4b8b663b31d`), worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. Everything I wrote is in `docs/research/100bit-spend-path-20261013/evidence/pin2-w3b-20261111/`, which is disjoint from W3a's files. That directory holds the edited sources (`sources/`), the untouched release originals with their git blobs (`release-originals/PROVENANCE.tsv`), the provenance of the unchanged rebuild sources (`sources-unchanged-PROVENANCE.tsv`), the compile log (`PIN2-W3b-COMPILE.tsv`, logs in `logs/`), notes on compile status (`COMPILE-STATUS-NOTES.tsv`) and the overlay hashes before and after (`overlay-PIN2.{before,after}.sha256`). The changes are in three commits, `186ab55e32f`, `39a36300d1a` and `41aa48f4a5e`, plus the commit that adds this report. Nothing was pushed, and nothing ran on the build host.

Compile method: W2's wrapper, copied as `PIN2W3b_compile.sh`. It runs one `lean -M7000 -DElab.async=false` at a time under a 180 s alarm, with `LEAN_PATH = overlay-PIN2 : objs : base`, and writes objects into `overlay-PIN2`. A waiting loop (`run.sh`) holds each job until no other `lean` process is running. No sorry, axiom, `native_decide` or raised heartbeat limit was used. Every credited `#print axioms` result reports only `propext`, `Classical.choice` and `Quot.sound`.

## 1. Serializer length and offset theorems (NHG_*): prepared, final form blocked on re-extraction

All ten NHG_* declarations are about the Aeneas-extracted `r0::Public::public_bytes`. They reach it through `NHG_Serializer.bytes`, `ExtractedPreparationSerializerWhole.toOld` and `Whole431.source_success`. Two things block their final form. First, the new body is not extracted yet: Stream C's PIN2 emission carries only `SemanticPublic` and its projection lemmas. Second, `toOld` and `NGX_COMBINED_IMPORT` sit under R0P.Core, so NHG_* has 5,239 stale imports and cannot compile coherently on this machine. I did not write uncompiled replacements.

Instead, the new module `PIN2_SerializerLengths` states the PIN2 byte image over the extracted input structs at the `PublicSerializerWhole431` level. That level does not depend on R0P.Core, so it compiles coherently now. The image mirrors W1's `loop_reference`:

`bytes q = (sourceSteps q).flatMap stepBytes ++ pool ++ deployment_domain ++ [has_destination] ++ destination?`

Proved, by named lemmas and `omega`, with no evaluation of large terms:

- **Lengths:** `prefix_length` gives 1455/1427, which is the frozen layout. `tail_length` gives 65/97. `length` gives 1520/1524. `bound` gives ≤ 1524.
- **Prefix:** `prefix_preserved`: the frozen bytes are a byte-identical prefix of the PIN2 body.
- **Offsets:** `tail_at_old_length` and `tail_offsets` fix the tail positions:
  - transfer: pool at 1455–1487, domain at 1487–1519, tag at 1519;
  - withdrawal: pool at 1427–1459, domain at 1459–1491, tag at 1491, destination at 1492–1524.

  These are the same offsets that W1's Rust test asserts.
- **Room:** `tail_room` gives room ≤ 1524 for each appended write. `prefix_room` keeps the frozen room `out + width ≤ 1455` for every prefix instruction. `init_frame` gives 75 + bytes = 1595/1599.
- **Producer forms:** `returned_of_refines` (≤ 1524) and `seed_size_of_refines` (≤ 57607) take an arbitrary producer plus the hypothesis `refines : produce q = ok (.Ok out) → out.val = bytes q`. That hypothesis is the open source-refinement obligation. It is not a cryptographic assumption, and it is not discharged here.
- **Teeth:** `old_length_superseded` proves the frozen length is no longer the output length.

The factoring has a consequence for the next worker. Suppose the PIN2 Whole431 model keeps `sourceSteps` as the prefix and appends the tail, either as new steps or as a raw-32 step. Then `NHG_Lengths.source`, `bound` and `prefix_room`, `NHG_ProducerDomains.words_room` and `frontier_room` (815), and `NHG_ProducerWidths.field_domain` keep their exact statements, because they talk only about `sourceSteps`. If the extraction instead folds the tail into `sourceSteps`, their 1455 becomes 1524 and `frontier_room`'s 815 must come from the structure. The total-length argument alone would give 884.

What changes for certain, once the refinement exists:

| Declaration | Old | New | Source of the new fact |
| --- | --- | --- | --- |
| `NHG_Lengths.returned` | ≤ 1455 | ≤ 1524 | `returned_of_refines` |
| `NHG_Lengths.digest_domain` | via ≤ 1455 | via ≤ 1524 (≤ 57607 holds) | `seed_size_of_refines` |
| `NHG_PublicCarrier.same_execution` | ≤ 1455 | ≤ 1524 | `returned_of_refines` |
| `NHG_PublicCarrier.begin_carrier` | statement unchanged | statement unchanged | needs only a rebuild after `same_execution` |

The `Step` type has no raw-bytes step, so `Whole431.program` cannot yet express `extend_from_slice` of a `[u8; 32]`. Adding one belongs to the Whole431 refinement of the re-extracted body.

## 2. Transcript record sizes

`WireBindingRecordCodec.Tx1Class.size` now gives `initTransfer => 1595` (was 1530) and `initWithdrawal => 1599` (was 1502). `tx1_class_safe` is re-proved with the same statement and proof (`c.size ≠ 65 ∧ c.size ≠ 31` for every non-node class). The rebuilt dependents that do not depend on R0P.Core are `SharedBinaryRecordGrammar`, `BinSharedGrammarBridge` and `WireTx2Records`. All three are unchanged sources, and all exit 0.

The new module `PIN2_Tx1InitRecordSize` ties the table to the parser so the constants are not free:

- `init_frame_size`: for every `parsePublic bytes = some pub`, the length of `PublicInitFrame.frame` equals the size of `initClass pub`. This uses W2's `parsed_init_frame_length` and would fail for the old table.
- `size_le_L`: every TX1 record class is ≤ 131072. The largest is the compact proof at 57,607.
- `init_transfer_size_unique` and `init_withdrawal_size_unique`: 1595 and 1599 each pick out exactly their own init class.

So `SelectedTranscriptParams.L = 131072` still covers everything, by proof: the init frames are at most 1599 and every class is at most 57,607.

The three other users need no source edit. `SelectedTranscriptParams.publicStatement`, `F3J_Public.from_cut` and `F3V_Public.from_decode` all close `75 + len ≤ L` by `omega` from W2's `parsed_init_fits` (≤ 1599). `R1SelectedTranscriptParams` did compile with its source unchanged (C026), but that compile is not credited (see section 4). `F3J` and `F3V` sit on 1,139 and 1,719 stale imports and belong to the build-host replay.

## 3. Parser work and the M10 budget: the budget is exceeded, so I stopped

`PublicParserWork` is re-proved against W2's parser. `decodeAfter` reads `readBytes32` twice and then `readDestination`, before the trailing-byte test. All value theorems keep their statements (`decodeAfter_value` through `parsePublic_value` equal `SemanticPublicWire.*`).

The new primitive `bytes32` charges a length scan, one comparison and one subtype constructor: `(length xs).2 + 2`, which is ≤ 35 on a 32-byte slice. That gives `readBytes32 ≤ 3·32 + 35 + 4 = 135` and `readDestination ≤ 138`. The work constants are recomputed exactly from the bind chain, and they are statement changes:

| Theorem | Old bound | New bound |
| --- | --- | --- |
| `decodeAfter_work` | 100282 | 100693 |
| `decodeTransfer_work` | 110000 (chain 109872) | 110283 |
| `decodeWithdrawal_work` | 110000 (chain 107824) | 108235 |
| `decode_work` | 110003 | 110285 |
| `parsePublic_work` | 110260 | 110542 |

`PublicParsedIndexM10.bound` rebuilt unchanged and exits 0. So did the unchanged allocation predecessors `OptionWorkBoundM10`, `AbstractStageSpecM10`, `AllocationStageSpecM10`, `ListConstructorAllocationM10` and `PublicCursorAllocationM10`.

**Budget check.** The M10 layer uses 110260 as a literal stage budget in three places:

- `PublicParserAllocationM10.spec` (`fun _ => 110260`);
- `ActualExtractorStagesM10.work` (`hp : … ≤ 110260`);
- `CostedExtractorStagesM10.workConstant := 4000000000000 + 110260 + …`, which flows into `CostedAllocationLedgerM10.workConstant`, `naturalConstant` and `scale`.

The proved bound now exceeds that budget by exactly **282** work units (110542 − 110260), on the transfer branch. The withdrawal branch alone fits with 1,765 to spare (108235 + 3 + 257 = 108495). The probe compile C010 confirms this mechanically: the unchanged `PublicParserAllocationM10` fails at `spec` with `≤ 110542` against an expected `≤ 110260`, and also on the `Common.mk` arity in its `decodeAfter`.

This is not an artefact of a generous tariff. The old transfer chain had only 129 units of slack inside 110260, and a single capped 32-byte cursor read already costs 3·32 + 4 = 100 in take/drop alone under the same tariff.

This is a proved upper bound exceeding the budget. I have not proved that the actual worst-case work exceeds it.

As instructed, I did not force the budget. I did not edit `PublicParserAllocationM10`, `ActualExtractorStagesM10` or `CostedExtractorStagesM10`, and no object for them is in the overlay.

The fix is a constant change, 110260 → 110542, at the three sites above. `PublicParserAllocationM10` also needs a cell model for `bytes32` and `readDestination`, its `decodeAfter` with 11 fields, and its `erase` proof re-run. The M10 constants are symbolic polynomial constants (with `4·scale³` the outermost form), and I found no numeric cap on `workConstant` downstream. So the change should leave the concrete bound's shape unchanged, but it is a change to a budget definition and is the lead's decision.

## 4. Rebuilds, and a coherence problem in the shared overlay

Rebuilt with unchanged sources in import order, all exit 0:

- the M10 predecessors and record-codec dependents listed above;
- `R0P.Semantics`, `SemSource`, `SemView`, `Sumcheck`, `Zerocheck` and `LaneMap`. These are on the `R1SelectedTranscriptParams` path. W3a also rebuilt `LaneMap` from the same source sha, and the overlay object is W3a's later one.

Three R0P sources had two blobs each: `LogUpAssembly`, `LogUpChain` and `SemRounds`. In each pair the blobs differ only by `set_option pp.fullNames true in` before `#print axioms`, so I used the `v8-r0-sem-proof` copies.

**Overlay problem, reported to the coordinator.** At 00:37:56, 36 symlinks appeared in `overlay-PIN2/R0P/`, pointing into `l187-closure/objs/R0P/`. They are not mine, and they look like a work-around for the `R0P/` directory shadowing. 33 of them (SemDecision, SemD2, SemD3, SemRounds, SemClosed, LogUpChain, LogUpAssembly, SemAssembly, Extraction, CopyInputLinks, CircleSampler, the Mask* family and others) are pre-PIN2 objects of modules that depend on R0P.Core. So any compile that imports them is not coherent. This tainted my C025 (`R1SelectedChallengeMapCore`) and C026 (`R1SelectedTranscriptParams`): I deleted both objects and do not credit them. None of my other compiles import a symlinked module; I checked each one's transitive imports.

The symlinks are also a hazard. Compiling one of those modules with `-o` into the overlay writes through the link and overwrites the shared closure object. My wrapper now refuses a symlinked target, and my order tool treats a symlink as not built. I did not remove the symlinks.

Overlay record: 30 files before, 83 regular files after. My objects, by sha256 prefix:

| Object | sha256 prefix |
| --- | --- |
| `PublicParserWork` | `614066ed` |
| `PublicParsedIndexM10` | `e6610fe4` |
| `OptionWorkBoundM10` | `3d54a883` |
| `AbstractStageSpecM10` | `ad0fa625` |
| `AllocationStageSpecM10` | `72df5eb1` |
| `ListConstructorAllocationM10` | `50f0fcfc` |
| `PublicCursorAllocationM10` | `dc733e07` |
| `WireBindingRecordCodec` | `a8b83f7a` |
| `SharedBinaryRecordGrammar` | `0ae24037` |
| `BinSharedGrammarBridge` | `f1e67a8f` |
| `WireTx2Records` | `6b7b0489` |
| `PIN2_Tx1InitRecordSize` | `0a5fa8a5` |
| `PIN2_SerializerLengths` | `51948b54` |
| `R0P/Semantics` | `0698eb36` |
| `R0P/SemSource` | `46cf3971` |
| `R0P/SemView` | `2dd7fa8b` |
| `R0P/Sumcheck` | `ff91c795` |
| `R0P/Zerocheck` | `8feb2546` |

Full hashes are in `overlay-PIN2.after.sha256`.

Scope of "depends only on W2's and my changes": computed over the import graph, that set is 10,552 modules, essentially the whole R0P.Core cone, and 50 of them are W2 impact-table owners needing edits. That is the coherent build-host replay, not a local job, so locally I stopped at the modules above.

## Compile table

Wall time is in seconds and peak RSS in GiB. Host swap during these runs was 7.1–7.2 GB (unchanged). The revision is the branch head at the time of each run (dirty worktree).

| id | file | exit | wall s | peak RSS GiB | note |
| --- | --- | --- | --- | --- | --- |
| C001 | PIN2W3b_Probe | 1 | 0.85 | 0.63 | probe: found the R0P/ shadowing |
| C002 | PIN2W3b_Probe | 1 | 2.13 | 2.06 | probe: field/namespace names |
| C003 | PublicParserWork | 0 | 9.33 | 2.68 | edited |
| C004 | PublicParsedIndexM10 | 0 | 1.81 | 2.66 | unchanged |
| C005 | OptionWorkBoundM10 | 0 | 1.90 | 2.67 | unchanged |
| C006 | AbstractStageSpecM10 | 0 | 1.91 | 2.68 | unchanged |
| C007 | AllocationStageSpecM10 | 0 | 1.88 | 2.68 | unchanged |
| C008 | ListConstructorAllocationM10 | 0 | 1.87 | 2.67 | unchanged |
| C009 | PublicCursorAllocationM10 | 0 | 1.95 | 2.68 | unchanged |
| C010 | PublicParserAllocationM10 | 1 | 10.01 | 2.67 | expected-failure probe (budget); no object |
| C011 | WireBindingRecordCodec | 0 | 1.21 | 1.15 | edited |
| C012 | SharedBinaryRecordGrammar | 0 | 0.93 | 1.18 | unchanged |
| C013 | BinSharedGrammarBridge | 0 | 1.01 | 1.18 | unchanged |
| C014 | WireTx2Records | 0 | 3.63 | 2.10 | unchanged |
| C015 | PIN2_Tx1InitRecordSize | 0 | 2.02 | 2.68 | new |
| C016 | PIN2_SerializerLengths | 1 | 1.93 | 2.08 | syntax |
| C017 | PIN2_SerializerLengths | 1 | 1.95 | 2.09 | offset proof |
| C018 | PIN2_SerializerLengths | 0 | 5.12 | 2.11 | new |
| C019 | R0P/Semantics | 0 | 2.06 | 2.68 | unchanged |
| C020 | R0P/SemSource | 0 | 2.77 | 2.82 | unchanged |
| C021 | R0P/SemView | 0 | 2.40 | 2.85 | unchanged |
| C022 | R0P/Sumcheck | 0 | 1.25 | 1.55 | unchanged |
| C023 | R0P/Zerocheck | 0 | 1.56 | 1.57 | unchanged |
| C024 | R0P/LaneMap | 0 | 8.25 | 2.76 | unchanged |
| C025 | R1SelectedChallengeMapCore | 0 | 1.89 | 2.83 | TAINTED (stale symlinked imports); object deleted |
| C026 | R1SelectedTranscriptParams | 0 | 1.93 | 2.84 | TAINTED; object deleted |

## Remaining blockers by owner

**Lead (decision):**

- The M10 budget: raise 110260 → 110542 in `PublicParserAllocationM10.spec`, `ActualExtractorStagesM10.work` and `CostedExtractorStagesM10.workConstant`, or choose another remedy. Once decided, `PublicParserAllocationM10` (cell model for `bytes32`/`readDestination`, 11-field `decodeAfter`, `erase`) is a focused edit that I can do.
- The overlay symlinks: replace them with real rebuilds, or with copies for the non-dependent LogUpFrac, MessageDescent and SemBadSets. Then `R1SelectedChallengeMapCore` and `R1SelectedTranscriptParams` (unchanged sources) need one coherent rebuild.

**Stream C:** extraction of the PIN2 `public_bytes` body, then the Whole431 refinement with a raw-32 step. That discharges the `refines` hypothesis of `PIN2_SerializerLengths` and lets the NHG_* edits in section 1 land: `returned`, `digest_domain` and `same_execution` to ≤ 1524, and the rest unchanged if the tail is appended after `sourceSteps`.

**W3a:** the first-layer and builder modules, and the R0P chain it is rebuilding. NHG_* also waits on `ExtractedDecoderPublicBinding` and `ExtractedPreparationSerializerWhole` being coherent.

**Build host (replay):**

- `F3J_Public` and `F3V_Public` need only a rebuild.
- `GSByteBankWorkM10`, `OptionWorkInvariantM10` and `AllocationOptionBindM10` (unchanged) and the rest of the 9,457 R0P.Core-tied dependents of `WireBindingRecordCodec`.
- The full cone in one coherent cold replay, then the axioms audit.

**Not mine (regenerated later):** the `NDO_JF*` devnet fixtures. They fix 1455 seed bytes, a 1530-byte init record and the row-18 header at offset 1530.

Obligations closed here: exact parser-work constants for the PIN2 parser; record sizes tied to the parser and re-checked against L; and lengths and offsets of the PIN2 byte image over the extracted input structs.

Obligations still open: the refinement of the re-extracted body, the M10 budget change, and the coherent replay.

Target not yet established.
