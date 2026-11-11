# PIN2 W6: the joint accepted fixture at the PIN2 pin

Worker W6, branch `fix/pin2-lean-20261110`, worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. The evidence directory is `docs/research/100bit-spend-path-20261013/evidence/pin2-w6-20261111/`, and the compile table is `PIN2-W6-COMPILE.tsv` in that directory. Every credited compile was one local `lean -M7000 -DElab.async=false` process under a 180 s alarm, through `PIN2W6_compile.sh`, started only when no other Lean process was running. The search path was `overlay-PIN2-W4 : overlay-PIN2 : overlay-HOST-P1 : objs : base`. overlay-HOST-P1 only appeared from batch A onward; it is the lead's read-only copy of the host phase-1 PASS objects. Objects were written only into `overlay-PIN2-W4`, through a temporary file and a rename. Nothing was written to objs, base, overlay-PIN2 or overlay-HOST-P1. Nothing was deleted and nothing was pushed. Superseded files are in `quarantine/`.

This is the final report. The lead stopped the local compile watcher at 13:05 UTC. The 172 fixture modules still uncompiled on the Mac wait on host modules at plan layers 276–293. According to the lead, none of those host modules has failed; they sit behind long unbuilt chains (FIn_Primitives…FIp_DotDecode, DrvC, CPP/P2P). The host now compiles every regenerated fixture module from the sources listed in §9, so the remaining compile checks are the host's.

## 1. Step 1: stale objects after the r0 clash fix

**Method.** `tools/Imports.lean` reads the import list out of each object file (`readModuleData`). `tools/PIN2W6_graph.py` builds the effective import graph from it, in LEAN_PATH order.

**Result.** 88 of the 249 W4/W5 objects had `PIN2_NEWGATE_r0` in their closure. They are `NDO_JFz_Scan00..59`, `NDO_JFz_Row00..26` and `NDO_JFz_RowGeometry`, and they reach r0 through `JFz_CanonicalAppend` and `PSem_Rows`. No other object was older than one of its imports.

- All 88 were recompiled with their source unchanged (C0001–C0088): 88 exit 0, 0 failed.
- Every log shows standard axioms only and no sorry. The longest compile was 48.6 s and the peak RSS 4.08 GB.
- Each rebuilt object is byte-identical to the one it replaced; only the mtimes changed.
- Before and after hash lists: `OVERLAY-PIN2-W4.before.sha256` and `OVERLAY-PIN2-W4.after-step1.sha256`. They are identical.

## 2. Exact claims established (compiled)

All of the following compiled with exit 0, with only `propext`, `Classical.choice` and `Quot.sound` on every `#print axioms` line, and no sorry. There were 403 compiles, 0 failures, and no rerun of a failed compile. Total wall time was 1,646 s, the longest compile 48.6 s (`NDO_JFz_RowGeometry`), and the peak RSS 4.43 GB.

| Batch | Compile ids | Modules |
| --- | --- | --- |
| Step 1 | C0001–C0088 | 88 JFz rebuilds |
| new modules | C0089–C0090 | `PIN2W6_SerializerProgram`, `PIN2W6_TranscriptSeed` |
| A | C0091–C0095 | DataProof14 (then quarantined, see §6), NativeHeader, HeaderFields, ScanAccepted, Parsed |
| C | C0096–C0259 | 164: RPt_JFq 49, RPt_JFn_Value 48, NDO_JFw 37 (all 27 NativeRows), RPt_JFn 16, RPt_JFo 10, JFv 2, JFr 1, JFu 1 |
| E | C0260–C0402 | 143: NDO_JFu_PublicDigest 47, NDO_JFt_Digest 47, the JFt snapshot/afterstate layer, the JFs serializer layer |
| G | C0403 | `RPz8_SCE_FixtureData` (non-fixture direct consumer) |

Of the 608 fixture-named modules in the release closure, 436 now have a coherent object in `overlay-PIN2-W4`; 172 remain (§5). Of the 51 non-fixture direct consumers, 1 is compiled.

**What the compiled regenerated modules state.** The statements are the release statements over PIN2 data:

- the checkpoint windows of the opening transcript and their decodes (`RPt_JFq_*`);
- the 22 PIN2 queries, which equal native tag 5 (`RPt_JFq_QueryWords`, `RPt_JFq_Queries`; `RPt_JFn_Value##_#.query` relates them to `JFo_Prepared.value.queries`);
- the PIN2 gamma words being canonical (`RPt_JFo_GammaCanonical`);
- the 47 + 47 statement digest windows and the snapshot/afterstate values (sequence and index 1, after-index 2);
- the decoded transfer (`output_lane` 2, checkpoint_sequence 0, anchor_sequence 0; `validate_common` and `validate_pool_v1_private_transfer_public_v1` hold with anchor_sequence 0, C0392);
- the native proof rows (`NDO_JFw_NativeRow00..26`).

**Section-7 restatements already compiled** (C0395–C0402):

- `NDO_JFs_SerializerCanonical.source : canonical ((PIN2_PublicBytesRefinement.steps value).flatMap PIN2Whole.stepWords)`, with `value : PIN2Whole.Public`.
- `NDO_JFs_SerializerSize.source : (… steps …).flatMap stepBytes).length = 1520`.
- `NDO_JFs_SerializerSource.source`: the PIN2 `public_bytes value = ok (.Ok encoded)`, its bytes, and length 1520.
- `NDO_JFs_PublicSerialization.source`: the same for the PIN2 `public_bytes (PreparationBinding.toPIN2 value)`.
- `NDO_JFs_SerializedBytes.source`: the PIN2 steps' bytes equal the 51 chunks with the index chunk `[1,0,…]`, followed by `JFs_Cell04.bytes` (pool), `JFs_Cell05.bytes` (domain) and `[0]`.
- `NDO_JFs_ExactSerialization`: `length = 1520`, and `source` on the PIN2 `public_bytes`.

Before and after text for each is in the in-file `PIN2 W6:` notes and in §4.

**New modules (W6, no release counterpart).**

- `PIN2W6_SerializerProgram` (C0089): `public_bytes q canon cap : ∃ encoded, PIN2 public_bytes q = ok (.Ok encoded) ∧ encoded.val = (steps q).flatMap stepBytes`. Its premises are those of the release `JFs_SerializerProgram.source`: canonical field words and capacity. Word and frontier steps reuse the frozen helper successes through W3b's `fields_eq` and `frontier_eq`.
- `PIN2W6_TranscriptSeed` (C0090) contains:
  - `domain_eq`: the PIN2 `DOMAIN` equals the release literal;
  - `new_of_length` and `source` for the PIN2 `SemanticTranscript.new`, over the release `TranscriptStep.initParts`;
  - `public_source` for the PIN2 `r1_semantic.public_transcript`;
  - `converted` at 1520;
  - `pin2Digest`, which carries a release `Digest32` to the PIN2 dictionary field for field.

These are source-helper and fixture theorems about one concrete accepted run. They close no premise of the security statement.

## 3. Regeneration method and what was reused

Each regenerated module was produced in one of three ways:

- **(a) An original 26 October generator, run verbatim.** `tools/PIN2W6_regen.py` runs it on research blob ids in a scratch tree. Check mode, on the research tree, must leave every file byte-identical (using the generator's own `--check` where it has one). Pin2 mode runs on a tree with every W4/W5/W6 PIN2 module and data file substituted under its JF name (`tools/PIN2W6_tree.py`, `TREE-SUBSTITUTIONS.json`). `Path.unlink` is disabled inside the generator process. The log is `REGEN-W6.jsonl`.
- **(b) The same generator with a hard-coded native literal substituted** (`tools/PIN2W6_subs.py` SUBS). In check mode the substitution computed from the 26 October native dump must be the textual identity, which proves the literal is that native value.
- **(c) A W6 generator for handwritten value-carrying modules** (`generators/PIN2W6_handwritten.py`). It substitutes exactly the literal sites, each matched by a pattern with a fixed count, in the release text. Check mode, using the 26 October checkpoint, statement and native values, reproduces every release text byte for byte (`HANDWRITTEN-check.json`). Pin2 mode output is in `HANDWRITTEN-pin2.json`.

| Generator (research) | Kind | Outputs (release names) |
| --- | --- | --- |
| `fixture-tx2-20261026/JFq_generate.py` | a, `--check` | 41 `RPt_JFq_*` |
| `fixture-tx2c-20261026/JFn_generate_values.py` | b, `query` = tx1 tag5 | 48 `RPt_JFn_Value##_#` |
| `fixture-tx2c-20261026/JFn_generate_arrays.py` | b, `q` = tx1 tag5 | 12 `RPt_JFn_Values##` |
| `fixture-tx2d-20261026/JFr_TX2_generate_slots.py` | a, `--check` | 48 `RPt_JFr_TX2_Slot##_#` |
| `joint-fixture10-20261026/JFp_generate_input.py` | geometry parametrized (PARAM) | `NDO_JFp_InitBytes` |
| W6 `PIN2W6_handwritten.py` | c | QueryWords, Queries, GammaCanonical, PaymentValue, PublicValue, SnapshotValue, SnapshotAcceptance, AfterstateValue, TransitionArithmetic, SeedBoundary |

The `JFp_generate_input.py` parametrization:

- public length 1455 → 1520, frame 1530 → 1595;
- 24 → 25 rest definitions, so 23 → 24 head SHA blocks;
- `JFs_Cell0*` chunks counted as 32 bytes.

With the 26 October geometry the parametrized script still reproduces the release text, which is a functional rather than textual identity, as in W4's `PIN2W4_sha.py`.

The section-7 proof restatements are hand edits of the release text. Each changed declaration carries a `PIN2 W6:` comment.

**Reused, not redone:**

- W4's byte, seed, scan, row, cell, metadata and digest-window sources;
- W5's transcript-layer sources and the native value dump `PIN2W5_VALUES.json` (no new native run);
- W3b's `PIN2_PublicBytesRefinement`, `PIN2_SerializerLengths`, `PIN2_SerializerTransport` and `PIN2_NHG_PublicCarrier`;
- W3c's `PIN2_PublicSerializerWhole`, `ExtractedDecoderPublicBinding` and `ExtractedPublicPreparationBinding` (`toPIN2`, `projection_eq`).

## 4. Literal changes and the values they were checked against

`LITERAL-CHANGES.tsv` holds each row with its compile id; `CHANGE-NOTES.tsv` attaches the same notes to the compile-table rows.

| Module | Literal | 26 Oct → PIN2 | Source / check |
| --- | --- | --- | --- |
| NDO_JFs_PaymentValue | anchor_sequence | 42 → 0 | statement [1736,1744) |
| NDO_JFs_PublicValue | output_lane; checkpoint_sequence | 3 → 2; 42 → 0 | statement byte 7; [104,112) |
| NDO_JFt_SnapshotValue / SnapshotAcceptance | sequence, next_pair_index | 13 → 1 | statement [288,304) |
| NDO_JFt_AfterstateValue | next_pair_index | 14 → 2 | statement [984,992) |
| NDO_JFu_TransitionArithmetic | n, n>>>1 | 13, 6 → 1, 0 | one-carry shape asserted; names `bit6`/`bit13` kept (not yet compiled) |
| NDO_JFs_SerializedBytes | index chunk + binding tail | 13 → 1; + pool, domain, [0] | statement [296,304), [1672,1736) |
| NDO_JFr_SeedBoundary | numeric | e4a92261…751e → 17667969…50a1 | native seed = W4 SeedHash (not yet compiled) |
| RPt_JFq_QueryWords/Queries, RPt_JFn_* | queries | [93499,…] → [46430,…] | checkpoint [320,408) = native tx1 tag5, asserted |
| RPt_JFo_GammaCanonical | gamma | [855639275,…] → [855536485,…] | checkpoint [176,208) = native tx1 tag4/27, asserted |
| NDO_JFp_InitBytes | length word, frame, blocks | 1455/1530/24 → 1520/1595/25 | root = PIN2 proof[16:48] (not yet compiled) |

The statement bytes are W4's `inputs/transfer-statement.bin` (sha256 `64eb9b43…c9fe`), which W4 and W5 cross-checked against the devnet recording.

**Correction to W4 §8.** W4 expected `JFs_PaymentValue` and `JFs_PublicValue` to compile unchanged because they name the cells. Each carries a 26 October literal, and four more handwritten modules do too (the table above).

## 5. Remaining, and why

**172 fixture modules in the closure are not compiled.** Every one is blocked by a host module that is not yet built:

| Host module | Fixture modules blocked |
| --- | --- |
| RPz7_FIp_DotsAdapter | 89 |
| NDO_Rc7_Top | 72 |
| RPz7_SAP_LiteralTop | 72 |
| RPt_JFr_TX2_DecodeCell | 63 |
| RPu_FIq_Terminal | 18 |
| RPt_JFr_TX2_ScalarCanon | 15 |
| RPt_FIo_WideValues | 14 |

A few more modules block fewer fixture modules each: the tier-2 JFy builders, RPu_JFs_TX2_Reduce and RPt_FIo_*. At 12:51 UTC the lead checked these on the host: none had failed, and they sit at plan layers 276–293 behind unbuilt chains.

By family, the 172 are:
- 48 `RPt_JFr_TX2_Slot` (sources regenerated);
- 24 `NDO_JFm_Q##Source` and the 5 `JFu_Claims*` (W5 sources);
- the remaining JFv, JFy, JFu-terminal and TX2 generic modules;
- the restated `NDO_JFu_OracleSeed`, `NDO_JFs_ExactInitialization`, `NDO_JFp_InitBytes`, `NDO_JFr_SeedBoundary` and `NDO_JFp_SHADigest`, and the regenerated `NDO_JFu_TransitionArithmetic`.

These are drafts that I expect to compile. They depend on `RPz7_F3V_OracleDictionary`, and their only unchecked step is the `rfl` linking `(pin2Digest D0).digest` to `rawOracle`. That is the same definitional step the release used.

**50 of the 51 non-fixture direct consumers** (for example `NKI_InitialPrefix`) are not compiled, and wait on the same blockers. A literal scan of all 4,765 non-fixture downstream modules found no 26 October native value. It covered every candidate blob where the release source is ambiguous (`NONJF-SCAN.json`, `NONJF-SCAN2.json`). The only length literals are 1455 in the NHG layer (`NHG_ProducerDomains`, `NHG_Lengths`, `NHG_PublicCarrier`), which is W3b's statement layer, not fixture data. These consumers are therefore expected to need a rebuild only, which is host phase 2.

**Not regenerated, because their outputs are outside the release closure:**
- the TX2 generators listed in W5's HARDCODED.json other than JFn (JFo_generate_query, JFs_TX2/JFw/JFz/JG*/JH*);
- W5's 53 out-of-closure blocked sources (JFr_Bytes, JFs_TX2_Geo, JFw_TX2_P, JFu_MaskInputs, Q25/Q26Source).

No in-closure module contains a 26 October native limb (`CLASSIFY.json`, plus the literal audit in §4).

## 6. overlay-PIN2-W4 state

`overlay-PIN2-W4` holds 563 regular files and no links; the hash list is `OVERLAY-PIN2-W4.final.sha256`. It is unchanged since the interim list.

- **Coherence** (`tools/PIN2W6_coherence.py`, `COHERENCE-*.json`): across the 563 objects and their closure of 4,374 modules, no local overlay object is older than one of its imports, and no release object in the closure imports an overlay object. One object is older than an import only because of copy times: `PIN2_SerializerLengths` (overlay-PIN2) is older than the overlay-HOST-P1 copy of `JFs_SerializerLengths`, and that copy is byte-identical to objs (`138567fe…`).
- **Quarantine:** C0091's `RPz8_JFx_DataProof14.olean` is byte-identical to the release object (`27a36f99…`; W4 found the PIN2 text identical). It was moved to `quarantine/overlay-PIN2-W4/` and recorded in `KEEP-RELEASE.tsv`, so that W4's `RPz8_JFx_NativeBytes` remains newer than its import.

## 7. Host interface

`HOST-NEED.tsv` lists 1,614 modules in import order: tier 1 has 1,570, for the statement layer and the 30 W5-blocked modules. It is computed on the object import graph. 47 of the listed modules are generic JF modules with no data dependence; the lead narrowed the phase-1 exclusion so the host builds them.

## 8. Axiom audit (whole log)

W7 found that the W-series wrappers read only the first line of a wrapped `#print axioms` list. I re-audited every Mac-side compile log with a whole-log parser (`tools/PIN2W6_axiom_audit.py`, `tools/PIN2W6_axiom_audit_all.py`). It reads each list across its continuation lines and also searches for `sorryAx`, `declaration uses 'sorry'` and error lines anywhere in the log. Each log is classified by the exit code in its worker's compile table.

| Worker | Logs | Credited (exit 0) | `#print axioms` results | Hits in credited logs | Uncredited logs with hits |
| --- | ---: | ---: | ---: | ---: | ---: |
| W4 | 153 | 151 | 10,441 | 0 | 2 |
| W5 | 98 | 98 | 40,312 | 0 | 0 |
| W3a | 761 | 736 | 2,513 | 0 | 25 |
| W3b | 37 | 31 | 236 | 0 | 6 |
| W3c | 2,553 | 2,518 | 12,335 | 0 | 34 |
| W6 | 403 | 403 | 7,079 | 0 | 0 |

The uncredited hits are the failed compiles each worker already recorded, whose errors elaborate to `sorryAx`. None of them left an object. The per-log results are in `AXIOM-AUDIT.json` (W6) and `AXIOM-AUDIT-ALL.json`.

`PIN2W6_compile.sh` now uses the whole-log check: any non-standard axiom name, including `sorryAx`, or any sorry forces exit 99. A positive test on probe P001 gives BAD=1, SORRY=3, EXIT=99.

## 9. Final regenerated sources (host handover)

`SOURCE-MANIFEST.json` gives every regenerated or new fixture module, with its final source path and sha256. There are 491 modules, each with exactly one file and no name in two directories. All 491 differ from the release text or are new.

| Directory | Modules | Compiled on the Mac (overlay-PIN2-W4) | Not yet compiled |
| --- | ---: | ---: | ---: |
| `evidence/pin2-w4-20261111/sources` | 141 (140 changed + `NDO_JFp_SHABlock25` new) | 141 | 0 |
| `evidence/pin2-w5-20261111/sources` | 179 | 96 | 83 (W5 BLOCKED.json; 53 outside the release closure) |
| `evidence/pin2-w6-20261111/sources` | 171 (169 changed + `PIN2W6_SerializerProgram`, `PIN2W6_TranscriptSeed` new) | 117 | 54 |

No regenerated module source lives anywhere else. Three locations hold files that are not module sources:

- `pin2-w5-20261111/generated/` holds generator data (JSON) and the archived row-25/26 monolith drafts (`JFm_UNCHECKED/*.lean.txt`). Those drafts are superseded by W5's compiled split modules and are not modules.
- `pin2-w5-20261111/handwritten/`, `pin2-w6-20261111/generated/` and `pin2-w6-20261111/handwritten/` do not exist. W6's handwritten-module generator writes into `sources/`.
- W4's two handwritten edits (`NDO_JFu_PublicHeader`, `NDO_JFu_PublicIndices`) are in W4's `sources/`.

`RPz8_JFx_DataProof14` is not regenerated. Its PIN2 text is identical to the release (`KEEP-RELEASE.tsv`).

## 10. Next concrete deliverable

The host compiles the 137 uncompiled regenerated sources (83 from W5 and 54 from W6) and the rest of the fixture-downstream closure from the sources in §9.

- If the host fails on a W6 module, isolate the declaration and change the generator or the restatement; never rerun it unchanged.
- The restated `NDO_JFu_OracleSeed`, `NDO_JFs_ExactInitialization` and `NDO_JFp_SHADigest` have one step not yet checked by Lean: the `rfl` equating `(pin2Digest D0).digest` with `rawOracle`.
- If that `rfl` fails, the likely fix is a `simp only [PIN2W6_TranscriptSeed.pin2Digest]` before it; this is a proof change, not a literal change.
- `NDO_JFu_TransitionArithmetic` (n = 1) and `NDO_JFr_SeedBoundary` are also unchecked by Lean.

This job closes no premise of the security statement. It restores the fixture so that the replay can run.

target not yet established
