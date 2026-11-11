# PIN2 W3b: serializer lengths, transcript record sizes, parser work and M10 budgets

Worker W3b, branch `fix/pin2-lean-20261110` (from W2 at `4b8b663b31d`), worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. Everything I wrote is in `docs/research/100bit-spend-path-20261013/evidence/pin2-w3b-20261111/`, which is disjoint from W3a's files. That directory holds the edited sources (`sources/`), the untouched release originals with their git blobs (`release-originals/PROVENANCE.tsv`), the provenance of the unchanged rebuild sources (`sources-unchanged-PROVENANCE.tsv`), the compile log (`PIN2-W3b-COMPILE.tsv`, logs in `logs/`), notes on compile status (`COMPILE-STATUS-NOTES.tsv`) and the overlay hashes before and after (`overlay-PIN2.{before,after}.sha256`). The changes are in commits `186ab55e32f`, `39a36300d1a`, `41aa48f4a5e`, `8c85c97c187`, `df5d7e799e3`, `27370a2924c`, `d824ca57908` and `3cd8ac8a9c1`, plus the commit that carries this revision of the report. Nothing was pushed, and nothing ran on the build host.

Compile method: W2's wrapper, copied as `PIN2W3b_compile.sh`. It runs one `lean -M7000 -DElab.async=false` at a time under a 180 s alarm, with `LEAN_PATH = overlay-PIN2 : objs : base`, and writes objects into `overlay-PIN2`. A waiting loop (`run.sh`) holds each job until no other `lean` process is running. No sorry, axiom, `native_decide` or raised heartbeat limit was used. Every credited `#print axioms` result reports only `propext`, `Classical.choice` and `Quot.sound`.

## 1. Serializer length and offset theorems (NHG_*)

**Update (after Stream C's re-extraction).** The refinement is now discharged and the final forms are proved; see section 5. The rest of this section describes the first stage, before the extracted body existed.

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

The three other users need no source edit. `SelectedTranscriptParams.publicStatement`, `F3J_Public.from_cut` and `F3V_Public.from_decode` all close `75 + len ≤ L` by `omega` from W2's `parsed_init_fits` (≤ 1599). `R1SelectedTranscriptParams` compiles with its source unchanged. My C026 is not credited (see section 4), but W3a's C0295 compiled the same source blob coherently on the real R0P chain. `F3J` and `F3V` sit on 1,139 and 1,719 stale imports and belong to the build-host replay.

## 3. Parser work and the M10 budget

**Update.** The lead decided to raise the budget from 110260 to 110542; see section 5. The rest of this section is the original budget check, which led to that decision.

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

The symlinks are also a hazard. Compiling one of those modules with `-o` into the overlay writes through the link and overwrites the shared closure object. My wrapper (`PIN2W3b_compile.sh`) now refuses to write to a symlink target (exit 4). `chain.sh` stops on a symlinked object, and `tools/order.py` treats a symlink as not built.

The coordinator has since resolved this. All 36 symlinks are deleted, `l187-closure/objs` and `base` are now read-only, and an mtime check showed no release object was modified. W3a has rebuilt the R0P.Core-dependent chain as real objects. W3a also rebuilt `R1SelectedChallengeMapCore` (C0281) and `R1SelectedTranscriptParams` (C0295) from the same release blobs, after its real SemD2 chain existed. Those coherent objects supersede my tainted C025/C026, so I did not rebuild them a second time.

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

## 5. After the lead's decisions and Stream C's re-extraction (2026-11-11)

### 5a. M10 budget raised from 110260 to 110542 (lead decision)

This is a constant of the extractor's work accounting. It was raised because the parser now performs three more reads, and it does not enter total(Q). Old value 110260, new value 110542, at three sites:

- **`PublicParserAllocationM10`: edited and compiled (C027, and C030 adding a comment only).**
  - `spec` now has budget `fun _ => 110542`.
  - The allocation model gains the binding suffix. `bytes32Cells` counts one subtype constructor; the 32 bytes themselves are already counted by `readCells`. `destinationCells` counts the tag and, for tag 1, one capped read. The new `paid` lemmas are `bytes32_paid` and `destination_paid`.
  - `decodeAfter` builds all 11 fields. Each model's `run` is literally the work function, so `erase` still closes by definition.
  - `erase`, `cells_work` and `allocated_bits_work` are unchanged statements.
- **`ActualExtractorStagesM10`:** literal changed at all four occurrences.
- **`CostedExtractorStagesM10`:** literal changed at all four occurrences, including `workConstant := 4000000000000+110542+…`.

The last two are written but not compiled. They still need 263 and 226 modules of W3a's chain, or the build-host replay. Their proofs are generic in the constant (`omega`/`nlinarith` over the same shape), so I expect no further edit, but that is not checked yet.

Other dependents of `PublicParserWork` were rebuilt unchanged with exit 0: `OptionWorkInvariantM10` (C028) and `AllocationOptionBindM10` (C029).

### 5b. `refines` discharged against the re-extracted body

The body is `PIN2_NEWGATE_r0` (file sha `92162163ae5b4017…`, object sha prefix `f9ade0b9`): Stream C's emission PCXQ_E001 at W1 source `271869c946d`. Three new modules, each compiling coherently now and depending on neither R0P.Core nor W3a:

**`PIN2_SerializerTransport` (C031)** transports the PIN2-extracted helpers into the checked 4.31 serializer helpers, for all outcomes, along the fixed error renaming:

- `fields_body_eq`, `fields_cont_decreases`, `new_fields_loop_unroll`, `fields_loop_eq` (well-founded on the real slice iterator), `fields_eq` and `frontier_eq`. The `PCWN_NewLib` branch and `from_residual` are unfolded inside the transport tactic.
- `fields_success` and `frontier_success`, derived from the release's `Success431.fields_success` and `Frontier431.frontier_success`.

The method and proofs are those of `ExtractedPreparationSerializerFields`, `ExtractedPreparationSerializerLoop` and `ExtractedPreparationSerializerWhole.frontier_eq`, restated for the PIN2 names.

**`PIN2_PublicBytesRefinement` (C032 and C033)** factors the body as a step program:

- It defines a PIN2 instruction program whose `Step` type has the old four instructions plus `raw` (`extend_from_slice` of an `[u8; 32]`).
- `source_eq_program`: the generated `public_bytes q` *is* `program (steps q) Vec.new`. The proof is `cases q <;> rfl`, the same method as the release's `Whole431.source_eq_program`; it compiles in 1.8 s at 2.1 GiB.
- `steps q` is the frozen 4bb3b3f instruction list followed by `raw pool`, `raw deployment_domain`, the `has_destination` byte and, for a withdrawal, `raw destination_token_account`.
- `program_success`: a successful run returns exactly `steps.flatMap stepBytes`.
- `steps_bytes`: that equals `PIN2_SerializerLengths.bytes (toOld q)`, where `toOld` maps the PIN2 carrier into the checked serializer's input type field for field.
- **`public_bytes_refines`**: `public_bytes q = ok (.Ok out) → out.val = PIN2_SerializerLengths.bytes (toOld q)`. This is the former `refines` hypothesis, now a theorem about the actual generated function. It has no capacity or allocator premise.
- `public_bytes_length`: a successful run returns exactly 1520 (transfer) or 1524 (withdrawal) bytes.

**`PIN2_NHG_Final` (C034, then C035 after the `single_width` fix)** gives the final PIN2 forms, stated over the PIN2 carrier and its generated `public_bytes`:

| Declaration | Old | PIN2 |
| --- | --- | --- |
| `source` | 1455/1427 over `sourceSteps` | unchanged |
| `bound` | ≤ 1455 | unchanged |
| `prefix_room` | ≤ 1455 | unchanged |
| `words_room` | ≤ 1455 | unchanged |
| `frontier_room` | ≤ 815 | unchanged |
| `field_domain` | ≤ 1880 | unchanged |
| `frontier_domain` | ≤ 1240 | unchanged |
| `returned` | ≤ 1455 | **≤ 1524**, on the actual PIN2 `public_bytes` |
| `digest_domain` premise | size ≤ 57607 via ≤ 1455 | `seed_size`: ≤ 57607 via ≤ 1524 |
| new: `tail_room`, `returned_layout` | — | every appended write ends ≤ 1524; a successful output is the frozen prefix followed by pool, domain, tag and destination |

Supporting lemmas are `first`, `prefix_nonempty`, `words_noninitial`, `frontier_noninitial`, `single_width` and `widths`.

So the six NHG statements named by the lead keep their constants (seven counting `frontier_domain`), and `returned` moves to ≤ 1524, as predicted in section 1. These are new PIN2 modules, not edits of the release NHG_* files: the release files stay valid for the frozen extraction.

**Still open in this item:**

- `NHG_Lengths.digest_domain` as a composition with `NGX_SemanticRuntime.seedViews`. That module depends on R0P.Core; its arithmetic premise is `seed_size`, proved here.
- `NHG_PublicCarrier.same_execution` and `begin_carrier`. These are about `r1_semantic::public_transcript`, which the PIN2 emission does not contain; it covers only the r0 module. Their only length fact is `returned` (≤ 1524, proved here). The open part is the PIN2 extraction of `public_transcript`, and the chain from it through `NGX_SemanticNew`.

Neither the emission nor these theorems prove that `public_bytes` succeeds on canonical inputs. They are success-conditional, like the release theorems.

`PRVEq_PIN2_ProcessCarry` is not used: nothing of mine touches the adapter.

My new objects: `PublicParserAllocationM10` `27645f94`, `OptionWorkInvariantM10` `45367752`, `AllocationOptionBindM10` `5baaa5d3`, `PIN2_SerializerTransport` `31da9fc2`, `PIN2_PublicBytesRefinement` `a958ccc5`, `PIN2_NHG_Final` `44017524`. Full hashes are in `overlay-PIN2.after.sha256`.

## Compile table

Wall time is in seconds and peak RSS in GiB. Host swap during these runs was 7.06–7.2 GB (unchanged). The revision is the branch head at the time of each run (dirty worktree).

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
| C026 | R1SelectedTranscriptParams | 0 | 1.93 | 2.84 | TAINTED; object deleted (superseded by W3a C0295) |
| C027 | PublicParserAllocationM10 | 0 | 6.00 | 2.70 | edited: suffix cells, budget 110542 |
| C028 | OptionWorkInvariantM10 | 0 | 1.77 | 2.66 | unchanged |
| C029 | AllocationOptionBindM10 | 0 | 1.84 | 2.66 | unchanged |
| C030 | PublicParserAllocationM10 | 0 | 5.93 | 2.70 | comment only |
| C031 | PIN2_SerializerTransport | 0 | 4.30 | 2.14 | new |
| C032 | PIN2_PublicBytesRefinement | 0 | 1.82 | 2.12 | new |
| C033 | PIN2_PublicBytesRefinement | 0 | 1.83 | 2.12 | unused simp argument removed |
| C034 | PIN2_NHG_Final | 1 | 1.63 | 2.08 | `decide` on a free singleton |
| C035 | PIN2_NHG_Final | 0 | 1.62 | 2.10 | new |

## Remaining blockers by owner

**Stream C:** the PIN2 extraction of `r1_semantic::public_transcript` (and its NGX_SemanticNew chain). That is needed for `same_execution` and `begin_carrier`; their length fact (≤ 1524) is already proved.

**W3a, or the build-host replay:**

- compiling `ActualExtractorStagesM10` and `CostedExtractorStagesM10` (budget literal already edited; 263 and 226 modules of the chain still needed);
- the `NGX_SemanticRuntime` composition for `digest_domain`;
- the first-layer and builder modules.

**Build host (replay):**

- `F3J_Public` and `F3V_Public` need only a rebuild.
- `GSByteBankWorkM10` and the rest of the 9,457 R0P.Core-tied dependents of `WireBindingRecordCodec`.
- The full cone in one coherent cold replay, then the axioms audit.

**Not mine (regenerated later):** the `NDO_JF*` devnet fixtures. They fix 1455 seed bytes, a 1530-byte init record and the row-18 header at offset 1530.

Obligations closed here:

- exact parser-work constants for the PIN2 parser;
- the M10 parser budget at 110542 in the allocation model (compiled), with the two extractor-stage sites edited;
- record sizes tied to the parser and re-checked against L;
- the source refinement of the re-extracted `public_bytes` to the PIN2 byte image, with no premise beyond successful return;
- the final PIN2 forms of the NHG_* lengths and offsets, `returned` at ≤ 1524.

Obligations still open: compiling the two extractor-stage modules, `digest_domain`/`same_execution`/`begin_carrier` (which need NGX and `public_transcript`), and the coherent replay.

Target not yet established.
