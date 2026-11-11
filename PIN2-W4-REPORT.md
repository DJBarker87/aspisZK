# PIN2 W4: regeneration of the recorded-bytes fixture from the PIN2 devnet run

Worker W4, branch `fix/pin2-lean-20261110`, worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. The evidence directory is `docs/research/100bit-spend-path-20261013/evidence/pin2-w4-20261111/`. The compile table is `PIN2-W4-COMPILE.tsv` at the worktree root. Every compile was one local `lean -M7000 -DElab.async=false` process under a 180 s alarm, started only when no other Lean process was running. Nothing ran on the build host, nothing was pushed, and no symlink was created. I edited no module outside the NDO_JF family and the fixture data modules it imports, and I did not touch W3c's files.

The short version is that the brief's premise does not hold. The fixture is not a set of 15 modules with a few length constants. It is a single concrete accepted run, and PIN2 changes its Fiat–Shamir seed, so the whole run has to be regenerated. I regenerated and compiled the part that depends only on recorded bytes and the SHA-256 seed: 151 objects, all on the standard axioms, including the two named roots `NDO_JFz_Scan50` and `NDO_JFz_Scan51`. The serializer root `NDO_JFs_SerializerCanonical` and every other module that needs the statement decoder cannot be compiled yet. A single W3c failure blocks them (section 3). The transcript-derived part of the fixture still needs inputs that no committed generator produces (section 8).

## 1. What the NDO_JF modules are and where their bytes came from

The NDO_JF family is not a devnet recording, and it was never re-pointed at the 10 November run. It is the "joint accepted fixture" built on 26 October by the JFx…JFq jobs (`evidence/joint-fixture*-20261026/`, `evidence/fixture-tx2*-20261026/`). Its three inputs are:

| Input | Release file | Bytes | sha256 |
| --- | --- | ---: | --- |
| Proof | `docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin` | 57,607 | `55386c50…6fff6f` |
| Statement (ASF8) | `…/transfer-13/r1-s2-public-asf8.bin` | 1,880 | `f6bcd494…05c331` |
| Checkpoint after TX1 | literal in `JFx_DataCheckpoint00` | 1,768 | `6c9f774d…3dc625` |

`JFx_generate_data.py` cut these into the 17 data modules `JFx_Data{Proof00..14,Public00,Checkpoint00}`. Later generators (scan, rows, records, statement windows, digests, cells, SHA blocks, transcript windows) and handwritten proofs were stacked on top.

On 28 October the NDO_ job (`evidence/native-reconcile-20261028/NDO_HANDOFF.md`) copied 3,118 witness modules to `lean/NDO_*` and changed only their import tokens. I confirmed this for the modules I regenerated: the JF source with its imports renamed equals the NDO_/RPz8_ release source byte for byte. Every NDO_JF source on `research` was last changed in that commit (`bc05e50bdce`, 2026-10-28). The host diagnostic's source hashes for `NDO_JFs_SerializerSize`, `NDO_JFz_Row17` and `NDO_JFz_Row18` equal those research blobs.

The fixture is a whole accepted run. The statement is serialized and hashed into the SHA-256 seed (`JFp_SeedHash`, `JFr_SeedBoundary`). Each of the 27 proof rows is absorbed and squeezed from that seed (`JFp_Query00*`, `JFm_Q01..Q26*`, each SHA step a literal). The verifier's later checks (`JFu`, `JFv`, `JFy`, `JFr`, and the TX2 `fixture-tx2*` families) are then evaluated at the challenges that come out. PIN2 lengthens the public bytes from 1,455 to 1,520, so the initialisation frame grows from 1,530 to 1,595 bytes, the seed changes, and every challenge downstream changes with it. The 26 October proof does not prove the PIN2 statement. The fixture can therefore only be rebuilt from a proof made under PIN2, which is the PIN2 devnet transfer.

## 2. Corrections to the W2 impact list

- **Five of W2's 15 modules match 1530 by coincidence.** `NDO_JFz_Row17.step`, `NDO_JFz_Row18.header/step`, `NDO_JFz_Parsed.rows18/accepted18`, `NDO_JFw_NativeRow18.bytes` and `NDO_JFw_Records.bytes` use 1530 as the proof-wire offset of row 18 (row 17 at 1077, plus a 5-byte header, plus 448 payload bytes). It is not the 75 + 1455 initialisation record. The PIN2 proof has exactly the same row geometry (checked: all 27 row headers and offsets are equal and the wire ends at 7031). The generated row and record sources are therefore text-identical under PIN2, and they compile unchanged on the PIN2 bytes (section 5).
- **The W2 list is far too small.** It is a literal scan for length constants. The real impact is every module whose content depends on the fixture's bytes or on its seed: the fixture's own modules plus 4,741 non-JF modules downstream of the data modules. Of those, 32 import fixture modules directly, for example `NKI_InitialPrefix`, `NHU_TransitionTotal`, `NJG_RoundDomains`, `NKR_TermHorner`, `NJU_*`, `RPu_FJf_*` and `RPt_FJi_*` (section 8).
- **The three "true roots" fail only because an import is missing.** The S4 diagnostics (`evidence/prov-p9g-20261110/diag/*.json`) say `unknown module prefix 'NDO_JFs_SerializerCanonical' / 'NDO_JFz_Scan50' / 'NDO_JFz_Scan51'`. Those objects were absent from the host view because the S4 run had excluded them. Their sources were never compiled there. `Scan50` and `Scan51` have no dependence on the public layout: they are canonicality scans of proof bytes at offsets 1082 and 1535. They were blocked only because their import `JFz_CanonicalAppend` was waiting for a rebuild, which W3c has since done.

## 3. The blocker for the serializer root and the statement layer

`NDO_JFs_SerializerCanonical` imports `NDO_JFs_PublicValue`. That module, and every statement-window module (`JFu_DigestSlice` → `JFu_DigestDecode`), reaches `RPz8_S6N_Installation`. W3c's driver skips that module along a chain of 26 modules that ends at one failure. The other non-JF blockers of the fixture chain end at the same root: `RPz7_F3V_OracleDictionary`, `RPz7_Op4P_Install`, `RPz7_PSem_Root`, `RPz7_PSem_RowStep` and `RPz7_SAP_SampleCanonical`. The root is:

```
PIN2W3c_C0880 RPz7_CurrentCompactInstalledPreparationV1 exit=1
error: import AspisR1FinishRelationCurrent.Types failed, environment already contains
'instDiscriminantErrorIsize' from PIN2_NEWGATE_r0
```

So W3c's import clash with `PIN2_NEWGATE_r0` blocks every statement-, serializer- and transcript-layer fixture module. W3c has to fix it before any of them can compile. I did not touch it.

## 4. PIN2 inputs and the independent cross-checks

`PIN2W4_inputs.py` (run with `python3 -I`) reads `/Users/dominic/aspis-lead-infra/pin2-run/receipts/PIN2_spend/{transfer,withdrawal}-stage1-recording.json` and writes `inputs/` and `INPUTS.json`. The checks below are asserts in that script and in `PIN2W4_crosscheck.py`:

1. Stage 1 (tag `[3,10]`, verifier `BLgzrkDi…`) reads the proof account `7raY4ZTe…` and the statement account `wfS9QEe1…` and writes the checkpoint `E2qRTHtQ…`. Proof and statement are identical before and after stage 1, and the checkpoint was all zero before it.
2. The proof account is 58,295 bytes: a 688-byte upload-program header followed by a 57,607-byte proof that starts with `R1P3CB18`. That is the same length and the same row geometry as the 26 October proof. The checkpoint written by the verifier on chain binds sha256(proof) at [16,48), sha256(statement) at [48,80) and the c1 root `proof[16:48]` at [112,144). This confirms both the header strip and the statement bytes against the deployed verifier's own record.
3. **Independent record.** I reassembled the statement account (1 upload transaction) and the proof account (16 upload transactions) from the upload-program instruction data (`tag, seed_len, seed, u32 offset, chunk`). Both are equal to the stage-1 account images.
4. **Public-bytes encoding.** A Python model of `r0::Public::public_bytes` reads the ASF8 statement at the Rust offsets (`pair_forest_terminal.rs`, `payment_relation.rs`, `pair_tree_profile.rs` at `c7593d23fdc`). On the 26 October statement it reproduces the release fixture's 1,455 public bytes, the 1,530-byte frame and the seed `e4a92261…751e`, which is `JFr_SeedBoundary.numeric`, all exactly. On PIN2 it gives 1,520 bytes for the transfer and 1,524 for the withdrawal. In the transfer, the pool is at public offset 1455, the domain at 1487 and `has_destination = 0` at 1519. The transfer frame is 1,595 bytes with seed `17667969…50a1`; the withdrawal frame is 1,599 bytes with seed `28f13624…80da`.
5. **Lean read-back** (`PIN2W4_crosscheck.py`, `CROSSCHECK.json`). This script parses the generated Lean sources, not the generators. The data-module literals concatenate to the recorded proof, statement and checkpoint; the sha256 values are below. Each of the 60 scan modules' literals equals `proof[off:off+n]` at its stated offset. The 23 changed statement-window modules equal `statement[off:off+n]`. The 26 SHA block inputs are exactly the SHA-256 padding of the PIN2 frame, whose length field is 1520 and whose slice [43, 1563) is the Python serialization. In that slice, the pool `statement[1672:1704]` sits at frame offset 1498 and the domain `statement[1704:1736]` at 1530.

| PIN2 transfer | Bytes | sha256 |
| --- | ---: | --- |
| proof (header stripped) | 57,607 | `354a754de5a2bbfcb505629695f9a3f719a2ee71c13aba7aabc5fef9714564cd` |
| statement account | 1,880 | `64eb9b432b5a806e1ad75b584d6adce60485b56313fdd4f9020be0a7914cc9fe` |
| checkpoint after stage 1 | 1,768 | `27bcbe250c1b629188ea40deb5592fd7b35541d24b20a13b62a9373ce9731652` |
| public bytes (§9 + binding tail) | 1,520 | `1930c1150fb983c3e5ef1f64da4dc01c3aa90829d1c7134ead603e436ee504a3` |
| initialisation frame | 1,595 | SHA-256 seed `17667969372a21c5833136bf944e8cc7fb0ab0e53ea40acfec66ca0afdd050a1` |

The fixture is the transfer, as it was on 26 October. The withdrawal inputs are extracted and checked too, but nothing is generated from them.

## 5. Mapping from the run record to the module constants

| Run record (transfer-stage1-recording.json) | Module(s) | Constants |
| --- | --- | --- |
| proof account `7raY4ZTe…` data[688:] | `RPz8_JFx_DataProof00..13` (14 changed), `DataProof14` (last 263 bytes, text-identical) | 32-byte chunk literals; `JFx_NativeBytes.proofBytes_length = 57607` unchanged |
| statement account `wfS9QEe1…` | `RPz8_JFx_DataPublic00` | 59 chunk literals; length 1880 unchanged |
| checkpoint `E2qRTHtQ…` post | `RPz8_JFx_DataCheckpoint00` | 56 chunk literals; length 1768 unchanged |
| proof[off:off+n], 60 regions (47 strict-scan + 13 compact payloads) | `NDO_JFz_Scan00..59` | 32-byte leaves `bNN`, canonicality per word; offsets and lengths unchanged (1082/1535 for Scan50/51) |
| proof row headers | `NDO_JFz_Row00..26`, `NDO_JFz_RowGeometry`, `NDO_JFw_NativeRow00..26` | unchanged text (headers and offsets identical) |
| statement[0:8] | `NDO_JFu_PublicHeader.first_eight` | byte 7 (`output_lane`) 3 → 2 |
| statement[288:296], [296:304], [984:992] | `NDO_JFu_PublicIndices` | sequence = next_pair_index 13 → 1, next 14 → 2 |
| 47 statement digest windows (`JFu_generate_public.py`) | `NDO_JFu_PublicDigestNN`, `NDO_JFt_DigestNN` | 13 changed: 00 historical anchor, 01 current root, 02/04/05 snapshot frontier[0,2,3], 22 next root, 24–26 next frontier[1–3], 43 payment anchor, 44 nullifier, 45 recipient, 46 change; 34 identical |
| statement metadata windows (`JFu_generate_metadata.py`) | `NDO_JFu_PublicMeta00..06` | changed: 02 live-snapshot pool (224), 04 sequence (288), 05 next_pair_index (296), 06 afterstate header and index (976, 16 bytes); 00, 01, 03 identical |
| statement cells (8,40,72,104,1672,1704,1736,1808) | `NDO_JFs_Cell00..07` | 00 master, 01 checkpoint account, 02 lane, 03 checkpoint sequence, 04 **pool**, 06 anchor sequence changed; 05 domain and 07 asset (77) identical |
| PIN2 frame (1,595 B = DOMAIN, 0, le32 1520, public bytes, c1 root) | `NDO_JFp_SHABlock00..25`, `NDO_JFp_SeedHash` | 26 SHA blocks (was 25; block 25 is a new module); seed state `17667969…` |

## 6. What was regenerated and how

All regeneration reruns the original generators, taken verbatim from `research` with their blob ids recorded in `REGEN.json` and `SHA.json`. The only substitutions are the input path and the input sha256 pins, plus, for the SHA generator, the frame-length literal (1530 → 1595) and the block count. Each patched generator is kept in `generators/`. `PIN2W4_regen.py check` first reran all nine generators on the 26 October inputs and reproduced every release source byte for byte (131 + 115 modules), including the NDO_/RPz8_ import renaming. The 26 October generator `JFp_generate_seed.py` hard-codes 25 blocks and a 58-byte tail, so `PIN2W4_sha.py` re-expresses it with the geometry as a parameter. Fed the 1,530-byte frame, it reproduces the release `NDO_JFp_SeedHash` byte for byte (asserted).

Two handwritten modules held statement values and were edited by hand: `NDO_JFu_PublicHeader` (one byte) and `NDO_JFu_PublicIndices` (two values). Their diffs are in section 7. Every other module I compiled is either a generator output or an unchanged release source. A module whose source is unchanged and compiles on the PIN2 data states a true fact about the PIN2 bytes.

Compiled into `overlay-PIN2-W4` (section 9), 151 objects, all exit 0, all `#print axioms` lines standard only, no sorry:

- 16 data modules plus `RPz8_JFx_NativeBytes` (rebuilt, unchanged source);
- 60 scans (`NDO_JFz_Scan00..59`, regenerated), `NDO_JFz_RowGeometry` and 27 rows (`NDO_JFz_Row00..26`, unchanged sources), so `Row17` and `Row18` are now compiled on PIN2 bytes;
- `NDO_JFu_PublicHeader`, `NDO_JFu_PublicIndices`, `NDO_JFu_PublicRange` and `NDO_JFu_PublicBindings`, the 8 cells and the 7 metadata windows `NDO_JFu_PublicMeta00..06`;
- 26 SHA blocks and `NDO_JFp_SeedHash`.

Generated but not compiled, because they are blocked by section 3: 26 changed digest-window sources (`NDO_JFu_PublicDigest*`, `NDO_JFt_Digest*`) and the text-identical rest of that layer. Generated, text-identical and not compiled: the 27 `NDO_JFw_NativeRow*`, blocked by `NDO_JFw_Frames` → `RPz7_PSem_*`.

## 7. Before and after of every changed statement

Changed by regeneration. The theorem names are kept and only literals move:

- `NDO_JFu_PublicHeader.first_eight`: `… .take 8 = [65,83,70,56,1,1,1,3]` → `[65,83,70,56,1,1,1,2]`.
- `NDO_JFu_PublicIndices`: `def before := [13,0,…]`, `def after := [14,0,…]`, `sequence : … = 13#u64`, `next : … = 14#u64` → 1, 2, `1#u64`, `2#u64`. The statements of `sequence_bytes`, `index_bytes`, `next_bytes` and `advance` are unchanged.
- `NDO_JFz_ScanNN`, `NDO_JFu_PublicDigestNN`, `NDO_JFu_PublicMetaNN`, `NDO_JFs_CellNN`, `NDO_JFt_DigestNN`, `RPz8_JFx_Data*`: only the `def bNN`, `def bytes`, `def cNN` and `def value` literals change. Every theorem statement refers to the same offsets and lengths.
- `NDO_JFp_SHABlockNN.checked : compress start (words input) = result`: the same statement over new `input`, `start` and `result` literals. `NDO_JFp_SHABlock25` is a new module.
- `NDO_JFp_SeedHash` (shape change, caused by the frame length):
  - `rawLength : raw.length = 1530` → `= 1595`
  - `headLength : head.flatten.length = 1472` → `= 1536` (23 → 24 head blocks)
  - `tailLength : tail.length = 58` → `= 59`
  - `tailPad : tail ++ [128] ++ List.replicate 61 0 ++ [0,0,0,0,0,0,47,208] = JFp_SHABlock23.input ++ JFp_SHABlock24.input` → `… List.replicate 60 0 ++ [0,0,0,0,0,0,49,216] = JFp_SHABlock24.input ++ JFp_SHABlock25.input`
  - `paddedLength : (pad raw).length = 1600` → `= 1664`
  - `checked : JFp_SHA256.hash raw = JFp_SHABlock24.result` → `= JFp_SHABlock25.result`
  - imports gain `NDO_JFp_SHABlock25`. The only in-family user of `checked`, `JFp_SHADigest.seed`, refers to it by name.

Statements that must change but are not yet written, because they are blocked (section 3). These are the targets for the PIN2 public serialization. The release form sits on the frozen `AspisR1PublicPreparation` / `AspisR1PublicSerializer.Whole431` extraction, which is no longer the deployed body:

- `NDO_JFs_SerializerCanonical`: `def value : Whole431.Public := toSerializer JFs_PublicValue.value` and `source : canonical ((sourceSteps value).flatMap stepWords)` → `value : PIN2Whole.Public` (W3c retargeted `toSerializer` to `RawBridge431.Public`, which is why the release text no longer type-checks), and `source : canonical ((PIN2_PublicBytesRefinement.steps value).flatMap PIN2Whole.stepWords)`. The binding tail contributes no field words (`raw`/`byte` steps), so the canonicality content is unchanged.
- `NDO_JFs_SerializerSize.source : ((sourceSteps …).flatMap stepBytes).length = 1455` → `((PIN2_PublicBytesRefinement.steps …).flatMap stepBytes).length = 1520`.
- `NDO_JFs_SerializerSource.source` and `NDO_JFs_PublicSerialization.source`: `… public_bytes value = ok (.Ok encoded) ∧ … ∧ encoded.val.length = 1455` → the PIN2 `AspisR1PublicPreparationPIN2…public_bytes (toPIN2 value)` with `= 1520`.
- `NDO_JFs_SerializedBytes.chunks`: the 51 chunks plus the appended `JFs_Cell04.bytes` (pool), `JFs_Cell05.bytes` (domain) and `[0#u8]`. The `index` lemma changes from `13#u64` to `1#u64`; the asset stays at 77.
- `NDO_JFs_ExactSerialization.length : JFs_SerializedBytes.bytes.length = 1455` → `= 1520`. `encoded` and `source` are restated on the PIN2 `public_bytes`.
- `NDO_JFu_TranscriptLength.converted (size : bytes.length = 1455) : … try_from … = ok (.Ok 1455#u32)` → 1520 and `1520#u32`.
- `NDO_JFu_OracleSeed.source`, `NDO_JFs_ExactInitialization.source`, `NDO_JFp_SHADigest.seed/source` and `NDO_JFp_InitBytes.native`: `initParts … root 1455#u32` → `1520#u32`. The transcript moves to `AspisR1PublicPreparationPIN2.r1_semantic.public_transcript` (W3b's `PIN2_NHG_PublicCarrier.same_execution`). `NDO_JFp_InitBytes.cast02`: `n02 = [175,5,0,0]` → `[240,5,0,0]`. Its 24 `stepNN` regroupings become 25.
- **Also required, and not in W2's list:** the generic lemma `NDO_JFu_TranscriptSeed.public_source` and its import `NDO_JFv_TranscriptInitial` are stated on the frozen `r1_semantic.public_transcript`. They need PIN2 counterparts before `OracleSeed` can be restated.

The rows and records modules (`Row17`, `Row18`, `Parsed`, `NativeRow18`, `Records`) need no statement change (section 2).

## 8. What remains for the fixture to be coherent

620 JF-named modules are downstream of the data. 124 of them are built here; the 27 SHA-layer objects are not downstream of the data. The other 496 fall into the three groups below, along with the non-JF consumers:

1. **Statement and serializer layer: sources generated, compile blocked by section 3.** This group is the 26 digest-window modules, the serializer and transcript-seed restatements listed in section 7, and the handwritten `JFs_PaymentValue`, `JFs_LateDecode`, `JFs_PublicValue` and `JFs_LateChildren`. The last four are expected to compile unchanged, because they reference the cells by name.
2. **Transcript-derived layer (`JFp_Query*`, `JFm_*`, `JFu` claims and circles, `JFv`, `JFy`, `JFr`, and the TX2 families `JFq/JFo/JFn/JFr_TX2/JFs_TX2/JFv_TX2/JFw`).** Their generators read diagnostic JSON files that no committed script writes: `JFm_WINDOWS.json` (the 27 absorb/read/ratchet SHA states per row), `JFr_coefficients.json`, `JFw_POWERS.json`, `JFw_RAW.json`, `JFw_HEADS.json`, `JFw_NUMERIC_PREFLIGHT.json` and `JFs_TX2_POINT_VALUES.json`. These hold verifier intermediate values (challenges, round coefficients, gamma powers, pairing pushes) for the old proof. For the PIN2 proof they have to be recomputed, either by an instrumented native verifier run on `inputs/transfer-proof.bin` and `transfer-statement.bin`, or by a Python verifier model checked against it. Only then can those generators be rerun. That is the next concrete deliverable: one job that produces these JSON files for the PIN2 transfer and checks them against the native verifier.
3. **Non-JF consumers.** 4,741 non-JF modules are downstream of the fixture data, 32 of them through a direct import. These include headline-path modules such as `NKI_InitialPrefix` (uses `JFy_Schedule.source` at the fixture public `p`), `NHU_TransitionTotal`, `NJG_RoundDomains`, `NKR_TermGatherPoseidon/Horner`, `NJU_*`, `RPu_FJf_*`, `RPt_FJi_*` and `RPz8_SCE_FixtureData`. Some of them state values of the old fixture and will need the same regeneration. They are outside the NDO_JF family, and I have not checked them.

Until all three groups land, the PIN2 fixture is only partly built, and the cold replay cannot reach the headline through it. The old fixture cannot simply be kept either. It is a run of the frozen 4bb3b3f `public_bytes`, which is no longer deployed, and attributing it to PIN2 would be the error that AGENTS §6 rules out.

## 9. Decision: a separate overlay

The brief said to write objects into `overlay-PIN2`. I wrote them to a new directory, `l187-closure/overlay-PIN2-W4`, searched first: `LEAN_PATH = overlay-PIN2-W4 : overlay-PIN2 : objs : base`. Putting PIN2 fixture data into `overlay-PIN2` would shadow the release data objects for all 5,361 modules downstream of them, while 496 fixture modules and the 4,741 non-JF consumers still carry 26 October facts. W3c's driver, and any S4 resync, would then build a mix of the two fixtures. A separate overlay keeps the swap reversible and atomic. Merge it into `overlay-PIN2` (a copy of regular files) only once groups 1 to 3 of section 8 are built in it. I did not write to `overlay-PIN2`, `objs` or `base`.

## 10. Compile table

153 compiles: 151 exit 0 (151 distinct objects), 2 failures, both fixed and recompiled. Total wall time 12.7 min. Longest compile 33.7 s. Peak RSS 3.96 GiB (`NDO_JFp_SeedHash`). Swap is not measured on macOS; `-M7000` caps the Lean heap. Every credited object's `#print axioms` lines name only `propext`, `Classical.choice` and `Quot.sound`. There is no sorry. Revision column: worktree HEAD at compile time, `984e1f8bff7`; the sources are this branch's uncommitted evidence files, committed afterwards. The full rows, with source sha256 and object hashes before and after, are in `PIN2-W4-COMPILE.tsv`.

Failures (both unchanged release sources whose statement holds a 26 October value; regenerated as in section 7):

- PIN2W4_C0080 NDO_JFu_PublicHeader: exit 1, 1.41 s (output_lane 3 in first_eight). Fixed in PIN2W4_C0107.
- PIN2W4_C0125 NDO_JFu_PublicIndices: exit 1, 1.41 s (sequence/index 13/14). Fixed in PIN2W4_C0126.

Every compile (id, file, exit, wall s, peak RSS bytes):

```
PIN2W4_C0001  RPz8_JFx_DataCheckpoint00     0   14.15  2324103168
PIN2W4_C0002  RPz8_JFx_DataProof00          0    5.05  2442133504
PIN2W4_C0003  RPz8_JFx_DataProof01          0    5.07  2443247616
PIN2W4_C0004  RPz8_JFx_DataProof02          0    5.12  2443476992
PIN2W4_C0005  RPz8_JFx_DataProof03          0    5.15  2443870208
PIN2W4_C0006  RPz8_JFx_DataProof04          0    5.16  2444115968
PIN2W4_C0007  RPz8_JFx_DataProof05          0    5.10  2443345920
PIN2W4_C0008  RPz8_JFx_DataProof06          0    5.10  2443935744
PIN2W4_C0009  RPz8_JFx_DataProof07          0    5.14  2444738560
PIN2W4_C0010  RPz8_JFx_DataProof08          0    5.06  2427682816
PIN2W4_C0011  RPz8_JFx_DataProof09          0    5.15  2439888896
PIN2W4_C0012  RPz8_JFx_DataProof10          0    5.10  2438938624
PIN2W4_C0013  RPz8_JFx_DataProof11          0    4.88  2419130368
PIN2W4_C0014  RPz8_JFx_DataProof12          0    4.91  2431123456
PIN2W4_C0015  RPz8_JFx_DataProof13          0    5.09  2427895808
PIN2W4_C0016  RPz8_JFx_DataPublic00         0    3.04  2326462464
PIN2W4_C0017  RPz8_JFx_NativeBytes          0    1.46  2273378304
PIN2W4_C0018  NDO_JFz_Scan50                0   13.04  3733487616
PIN2W4_C0019  NDO_JFz_Scan51                0    5.76  3732275200
PIN2W4_C0020  NDO_JFz_RowGeometry           0    2.10  3657433088
PIN2W4_C0021  NDO_JFz_Row00                 0    2.34  3667869696
PIN2W4_C0022  NDO_JFz_Row01                 0    2.34  3668754432
PIN2W4_C0023  NDO_JFz_Row02                 0    2.34  3666935808
PIN2W4_C0024  NDO_JFz_Row03                 0    2.37  3666640896
PIN2W4_C0025  NDO_JFz_Row04                 0    2.35  3668459520
PIN2W4_C0026  NDO_JFz_Row05                 0    2.39  3668885504
PIN2W4_C0027  NDO_JFz_Row06                 0    2.42  3666640896
PIN2W4_C0028  NDO_JFz_Row07                 0    2.37  3666788352
PIN2W4_C0029  NDO_JFz_Row08                 0    2.37  3667017728
PIN2W4_C0030  NDO_JFz_Row09                 0    2.36  3668525056
PIN2W4_C0031  NDO_JFz_Row10                 0    2.37  3665838080
PIN2W4_C0032  NDO_JFz_Row11                 0    2.37  3667394560
PIN2W4_C0033  NDO_JFz_Row12                 0    2.43  3666690048
PIN2W4_C0034  NDO_JFz_Row13                 0    2.37  3667148800
PIN2W4_C0035  NDO_JFz_Row17                 0    2.34  3667623936
PIN2W4_C0036  NDO_JFz_Row18                 0    2.34  3666526208
PIN2W4_C0037  NDO_JFz_Scan00                0   10.47  3850960896
PIN2W4_C0038  NDO_JFz_Scan01                0    6.78  3824041984
PIN2W4_C0039  NDO_JFz_Scan02                0   33.71  4077993984
PIN2W4_C0040  NDO_JFz_Scan03                0   11.38  3845652480
PIN2W4_C0041  NDO_JFz_Scan04                0    4.15  3781410816
PIN2W4_C0042  NDO_JFz_Scan05                0   12.35  3864952832
PIN2W4_C0043  NDO_JFz_Scan06                0    4.35  3803594752
PIN2W4_C0044  NDO_JFz_Scan07                0   13.11  3880337408
PIN2W4_C0045  NDO_JFz_Scan08                0    3.45  3695886336
PIN2W4_C0046  NDO_JFz_Scan09                0    9.23  3798745088
PIN2W4_C0047  NDO_JFz_Scan10                0    3.70  3727884288
PIN2W4_C0048  NDO_JFz_Scan11                0   10.32  3826614272
PIN2W4_C0049  NDO_JFz_Scan12                0    3.95  3756474368
PIN2W4_C0050  NDO_JFz_Scan13                0   11.36  3839950848
PIN2W4_C0051  NDO_JFz_Scan14                0    4.18  3782361088
PIN2W4_C0052  NDO_JFz_Scan15                0   12.44  3862167552
PIN2W4_C0053  NDO_JFz_Scan16                0    4.35  3804315648
PIN2W4_C0054  NDO_JFz_Scan17                0   13.86  3875602432
PIN2W4_C0055  NDO_JFz_Scan18                0    3.88  3698606080
PIN2W4_C0056  NDO_JFz_Scan19                0   10.06  3798695936
PIN2W4_C0057  NDO_JFz_Scan20                0    4.17  3729997824
PIN2W4_C0058  NDO_JFz_Scan21                0   10.68  3822501888
PIN2W4_C0059  NDO_JFz_Scan22                0    3.96  3787587584
PIN2W4_C0060  NDO_JFz_Scan23                0   11.51  3847258112
PIN2W4_C0061  NDO_JFz_Scan24                0    4.19  3784966144
PIN2W4_C0062  NDO_JFz_Scan25                0   12.52  3866001408
PIN2W4_C0063  NDO_JFz_Scan26                0    4.39  3804086272
PIN2W4_C0064  NDO_JFz_Scan27                0   12.34  3872292864
PIN2W4_C0065  NDO_JFz_Scan28                0    3.87  3700932608
PIN2W4_C0066  NDO_JFz_Scan29                0    9.62  3795320832
PIN2W4_C0067  NDO_JFz_Scan30                0    4.05  3764748288
PIN2W4_C0068  NDO_JFz_Scan31                0   10.64  3830431744
PIN2W4_C0069  NDO_JFz_Scan32                0    4.04  3756556288
PIN2W4_C0070  NDO_JFz_Scan33                0   11.58  3842523136
PIN2W4_C0071  NDO_JFz_Scan34                0    4.23  3785637888
PIN2W4_C0072  NDO_JFz_Scan35                0   12.62  3866624000
PIN2W4_C0073  NDO_JFz_Scan36                0    4.50  3807297536
PIN2W4_C0074  NDO_JFz_Scan37                0   11.73  3864428544
PIN2W4_C0075  NDO_JFz_Scan38                0    3.54  3703291904
PIN2W4_C0076  NDO_JFz_Scan39                0    9.47  3802578944
PIN2W4_C0077  NDO_JFz_Scan40                0    3.77  3735142400
PIN2W4_C0078  NDO_JFz_Scan41                0   10.58  3832659968
PIN2W4_C0079  NDO_JFz_Scan42                0    3.99  3791110144
PIN2W4_C0080  NDO_JFu_PublicHeader          1    1.41  2238054400
PIN2W4_C0081  NDO_JFz_Scan43                0   11.24  3849191424
PIN2W4_C0082  NDO_JFz_Scan44                0    4.12  3787128832
PIN2W4_C0083  NDO_JFz_Scan45                0   12.45  3867443200
PIN2W4_C0084  NDO_JFz_Scan46                0    4.36  3809083392
PIN2W4_C0085  NDO_JFz_Scan47                0    2.48  3666116608
PIN2W4_C0086  NDO_JFz_Row14                 0    2.48  3666313216
PIN2W4_C0087  NDO_JFz_Scan48                0    6.65  3738222592
PIN2W4_C0088  NDO_JFz_Row15                 0    2.39  3666657280
PIN2W4_C0089  NDO_JFz_Scan49                0    6.45  3736125440
PIN2W4_C0090  NDO_JFz_Row16                 0    2.39  3666591744
PIN2W4_C0091  NDO_JFz_Scan52                0    5.58  3729211392
PIN2W4_C0092  NDO_JFz_Row19                 0    2.33  3668164608
PIN2W4_C0093  NDO_JFz_Scan53                0    5.38  3723788288
PIN2W4_C0094  NDO_JFz_Row20                 0    2.34  3664609280
PIN2W4_C0095  NDO_JFz_Scan54                0    5.22  3723313152
PIN2W4_C0096  NDO_JFz_Row21                 0    2.28  3662266368
PIN2W4_C0097  NDO_JFz_Scan55                0    4.94  3719249920
PIN2W4_C0098  NDO_JFz_Row22                 0    2.29  3663347712
PIN2W4_C0099  NDO_JFz_Scan56                0    5.50  3732930560
PIN2W4_C0100  NDO_JFz_Row23                 0    2.28  3661840384
PIN2W4_C0101  NDO_JFz_Scan57                0    7.30  3767566336
PIN2W4_C0102  NDO_JFz_Row24                 0    2.44  3676471296
PIN2W4_C0103  NDO_JFz_Scan58                0   28.44  3986194432
PIN2W4_C0104  NDO_JFz_Row25                 0    2.48  3695951872
PIN2W4_C0105  NDO_JFz_Scan59                0   10.01  3841146880
PIN2W4_C0106  NDO_JFz_Row26                 0    2.66  3759128576
PIN2W4_C0107  NDO_JFu_PublicHeader          0    1.40  2258386944
PIN2W4_C0108  NDO_JFu_PublicRange           0    1.61  2287910912
PIN2W4_C0109  NDO_JFs_Cell00                0    1.50  2267414528
PIN2W4_C0110  NDO_JFs_Cell01                0    1.49  2267709440
PIN2W4_C0111  NDO_JFs_Cell02                0    1.51  2267791360
PIN2W4_C0112  NDO_JFs_Cell03                0    1.48  2266169344
PIN2W4_C0113  NDO_JFs_Cell04                0    1.45  2265366528
PIN2W4_C0114  NDO_JFs_Cell05                0    1.45  2264547328
PIN2W4_C0115  NDO_JFs_Cell06                0    1.43  2263826432
PIN2W4_C0116  NDO_JFs_Cell07                0    1.44  2263810048
PIN2W4_C0117  NDO_JFu_PublicMeta00          0    1.50  2267365376
PIN2W4_C0118  NDO_JFu_PublicMeta01          0    1.54  2268332032
PIN2W4_C0119  NDO_JFu_PublicMeta02          0    1.51  2266873856
PIN2W4_C0120  NDO_JFu_PublicMeta03          0    1.49  2266939392
PIN2W4_C0121  NDO_JFu_PublicBindings        0    1.40  2260402176
PIN2W4_C0122  NDO_JFu_PublicMeta04          0    1.55  2266398720
PIN2W4_C0123  NDO_JFu_PublicMeta05          0    1.53  2265759744
PIN2W4_C0124  NDO_JFu_PublicMeta06          0    1.47  2265743360
PIN2W4_C0125  NDO_JFu_PublicIndices         1    1.41  2240839680
PIN2W4_C0126  NDO_JFu_PublicIndices         0    1.38  2263351296
PIN2W4_C0127  NDO_JFp_SHABlock00            0    2.58  2621833216
PIN2W4_C0128  NDO_JFp_SHABlock01            0    2.55  2622373888
PIN2W4_C0129  NDO_JFp_SHABlock02            0    2.58  2621865984
PIN2W4_C0130  NDO_JFp_SHABlock03            0    2.56  2622406656
PIN2W4_C0131  NDO_JFp_SHABlock04            0    2.57  2622636032
PIN2W4_C0132  NDO_JFp_SHABlock05            0    2.59  2621702144
PIN2W4_C0133  NDO_JFp_SHABlock06            0    2.62  2621554688
PIN2W4_C0134  NDO_JFp_SHABlock07            0    2.61  2622488576
PIN2W4_C0135  NDO_JFp_SHABlock08            0    2.61  2619588608
PIN2W4_C0136  NDO_JFp_SHABlock09            0    2.63  2622226432
PIN2W4_C0137  NDO_JFp_SHABlock10            0    2.64  2621538304
PIN2W4_C0138  NDO_JFp_SHABlock11            0    2.62  2618851328
PIN2W4_C0139  NDO_JFp_SHABlock12            0    2.62  2619670528
PIN2W4_C0140  NDO_JFp_SHABlock13            0    2.63  2621898752
PIN2W4_C0141  NDO_JFp_SHABlock14            0    2.64  2622193664
PIN2W4_C0142  NDO_JFp_SHABlock15            0    2.66  2621947904
PIN2W4_C0143  NDO_JFp_SHABlock16            0    2.62  2618982400
PIN2W4_C0144  NDO_JFp_SHABlock17            0    2.63  2622029824
PIN2W4_C0145  NDO_JFp_SHABlock18            0    2.63  2621865984
PIN2W4_C0146  NDO_JFp_SHABlock19            0    2.65  2621947904
PIN2W4_C0147  NDO_JFp_SHABlock20            0    2.63  2618654720
PIN2W4_C0148  NDO_JFp_SHABlock21            0    2.64  2619277312
PIN2W4_C0149  NDO_JFp_SHABlock22            0    2.64  2622046208
PIN2W4_C0150  NDO_JFp_SHABlock23            0    2.64  2622472192
PIN2W4_C0151  NDO_JFp_SHABlock24            0    2.65  2621964288
PIN2W4_C0152  NDO_JFp_SHABlock25            0    2.64  2618851328
PIN2W4_C0153  NDO_JFp_SeedHash              0    6.56  4252565504
```

## 11. Overlay hash list after

`/Users/dominic/aspis-lead-infra/l187-closure/overlay-PIN2-W4`: 151 regular files, no links. Before this job the directory did not exist, so there is no before list. `overlay-PIN2` was not written. The before/after 16-hex-digit prefix of every object is in the TSV; the full sha256 list is `OVERLAY-PIN2-W4.sha256`:

```
efcf20d05417525197f0a993feab4614bc9ad3d114574c95560a7385b3dc5abd  NDO_JFp_SeedHash.olean
907f46e29a741543946360b3e72f7a4c7bf139e284ded1c7f1179e026064e7a0  NDO_JFp_SHABlock00.olean
8feab5c280888b81f667ae42c363fc5ceb30212c7d906fdaaec158601985766a  NDO_JFp_SHABlock01.olean
d7bebf5fd7d9117f6d9d7d9898b2e1ace00307c37045800389670fa066c9327d  NDO_JFp_SHABlock02.olean
968b306aa16d1e2bbb8d9c5de59679fa51e24d95883acdd52d446a32fb0bc2f8  NDO_JFp_SHABlock03.olean
70bd8c8994a99e872f9d687796c6ecf9d5d411ed98eaa720ccce4c60e4dec695  NDO_JFp_SHABlock04.olean
1d18642025d12fc138111cfb138f0ed300ad577adaba1d9764e1a93f8ffd90ae  NDO_JFp_SHABlock05.olean
3d3e91d38d547ec16d36fe574cfa7060fef84c5c952ecd59192dfec537bcc2e9  NDO_JFp_SHABlock06.olean
28c15169744588e6d9d8af2cc0d58f91f68cc4ce91d745529fa1ea1fef8f8af6  NDO_JFp_SHABlock07.olean
4bf5fb6678ec9ca4d9102a8586176a4f0cebd73d0c41a1abe18736f9fa6bcd08  NDO_JFp_SHABlock08.olean
f102162fbf79027b010fa0dd74c19b450f4622e4835f31ea532d78d7bcdaff8f  NDO_JFp_SHABlock09.olean
27efc141c04c121aef895d5873b2f75ecc66bd1ee6d19a742f3022c955a2766b  NDO_JFp_SHABlock10.olean
472ba5fd91eb904565e543d0d6771bf570f1f8b1fdc16957623571899ac2209e  NDO_JFp_SHABlock11.olean
86c9fd923f616f42ef880e0e7edbad5d30d9a0187acf817b74a75d4201148826  NDO_JFp_SHABlock12.olean
beeff5197b612bd23088bc1d4d4795e445290cbc5a25832d33ec49a349fb1db3  NDO_JFp_SHABlock13.olean
ab2e36f7ffc5c91ac98595019c35dbe06ba434205bada27e82eb675fc9da77dc  NDO_JFp_SHABlock14.olean
690635b2d165bf8be7a90272f6d9f992c7cd4f3b35089d7c5d7cd34c40ab43c3  NDO_JFp_SHABlock15.olean
b921bb13de140c819fcb043fd90765b772a2fd7c3cd3d8e1e09a3611136b8b7b  NDO_JFp_SHABlock16.olean
b5797528582a015bf8aa00fbde6e23c98f810d66de7160913619ccc925d71bcb  NDO_JFp_SHABlock17.olean
d5e7fb80ec6199e3dd236ef53b0e00b8635ceb76edd2a40e43f1af8637414af8  NDO_JFp_SHABlock18.olean
eed9b8a2a73f19ecda971d9dd74928887b7f6acd3aad2482a99096e5dc0edddc  NDO_JFp_SHABlock19.olean
3ecef13f5354fdfa24f6aa364577cecb98dd18bd9bbb3aee0a2c3279f9f9d306  NDO_JFp_SHABlock20.olean
78661381c1413d0cce5de5023786d2b46fe2fa995faf70f42cfa803099156973  NDO_JFp_SHABlock21.olean
6ed846285e119d4c91e990c215aba92a8c6915a0c686865c3aeffe1e871ac8b1  NDO_JFp_SHABlock22.olean
6c3055032999f2952cac26d12ccd617009a5d1425d1bf9bd73a8976f3ff70c31  NDO_JFp_SHABlock23.olean
66f82fe26cc138b0db9fff8a5fb48b05ae7c2dbaf42190eef638e2980a1f01af  NDO_JFp_SHABlock24.olean
5095d51d0c764ce2331ed29ea2784fc3547866a34c5db7923f99ed2963507cd6  NDO_JFp_SHABlock25.olean
6a0948c80b75196399261c84f7dadf458938d3d13474fd857e91e0ff912373cf  NDO_JFs_Cell00.olean
ee01d3ae92040a89726a3c9aeab1e9dc3298b72f034396ddb6cc7aabf19d49f4  NDO_JFs_Cell01.olean
6fe33dcc66f49b45409176438a94fdba1d2045c7ab3a0221a92da5da7cbd66df  NDO_JFs_Cell02.olean
451c53a9d09d8ca2d79c97e2ce208a4803fea40fc80269a24273eb75e18e6ede  NDO_JFs_Cell03.olean
13ac02c9c214cfdd38db4deb0af37f59fbbfa4be805e5e4aadd7fddfd96f9d67  NDO_JFs_Cell04.olean
a6af99abe31b0b0848e8378db310548c8cae786ac10ebf59c65e093a7fddd705  NDO_JFs_Cell05.olean
5d846eb405c4d1af08f23ec08e6ba51c1278f149d6bc2597377b1f3113babcdf  NDO_JFs_Cell06.olean
5d30c589ffefbce3744ce85479491383eb720a513483e8c6013834ec350b568d  NDO_JFs_Cell07.olean
eaf7710d0f6c261940369cbf54c6b1adafd9c766a7267836fe1197e789864b59  NDO_JFu_PublicBindings.olean
5957860535ca71db2ed0e2eec242fdc036229f5a5d47428a5b546c8078f14526  NDO_JFu_PublicHeader.olean
3f6bad10f9267f64487a26543d6d6c7eca2fb61322b53fffa2c2f4c1572fa60c  NDO_JFu_PublicIndices.olean
bf926f5051144df4db1f745bf607ff5a0b0881271784790e8ca47d78a1b3b15a  NDO_JFu_PublicMeta00.olean
c5be4679817f4bf0c0284044262f13a50c9a276c6c8c05d06a1f25579f6ecd40  NDO_JFu_PublicMeta01.olean
deda72e36fcbf4086c24802b8857ffbd5d62368b55d38e985d70a950bf676915  NDO_JFu_PublicMeta02.olean
edf4684d5f9c9aba27c0c33a7503f19980025b0c5f6c6aecaafc0b9b66e27b98  NDO_JFu_PublicMeta03.olean
0f0ed29bded320f4075c7a757203791a214a5c741a3d7bc08fa701f001a320ed  NDO_JFu_PublicMeta04.olean
6829f0081a11c0cf6120cc00285852cde1c3dec3db9da28116e09261fb53e0cb  NDO_JFu_PublicMeta05.olean
d82a386b3c3953a71c2f0cd6f28207c7f7aba1ca938ddc125d75e1996a02927b  NDO_JFu_PublicMeta06.olean
df79d82cce9304f7a15f58c4c89b53f20af024dd14e7782dbbbe595e01f1cf65  NDO_JFu_PublicRange.olean
ce9abc04c445241dcb1c6d33cf66cdacb0e754e68f2e55a085a4145cceafa15b  NDO_JFz_Row00.olean
f06bc1a1385a0c3163676103252d63f8409ef8e913e03de6124fb54bd1bd0735  NDO_JFz_Row01.olean
8ee0c12865a4b4be641787ffc75d7f838fd88f1f8fa58ce71203ebc6578b013b  NDO_JFz_Row02.olean
92173d2e85ef9607a954fee2027f8ae4302e9a14da1d461a69c8b129f53fb373  NDO_JFz_Row03.olean
cf936bbd8870211a5e7c59611e58c464d44ef6496b9f026e38f524d4c4a36948  NDO_JFz_Row04.olean
c20a7d2a0107c2cda3c66b358bc3946222a3d22486dfb38e7c925e34a5be20e5  NDO_JFz_Row05.olean
dd9a80064cc856acdd78a971abcb0a2d7926fafa45c1d0dc9172b4df5c7ef4cf  NDO_JFz_Row06.olean
6723952b8d16d9eeca247af67d50f303bb1a3680f289d2ae1b3d140ec4e638f8  NDO_JFz_Row07.olean
965543f57f1e5cbf98e6b0aea018247096e82cd5ae8a0d06c207552bf17a85fd  NDO_JFz_Row08.olean
cf19a4076c314530cfb4e354d46a034923984cc228f2621aaa93ce60c8a6e375  NDO_JFz_Row09.olean
5a6127ec9b72e81635b0763d8602abde118202ff17dd2312ce51eb64123119a7  NDO_JFz_Row10.olean
858e212f0baed7ce21e2379de27a8397c67e25a62dfaeac6215e92b4de4e5d2d  NDO_JFz_Row11.olean
1475348955812f46766989f757212ed78d8699dbedc719e12f308f55685d474d  NDO_JFz_Row12.olean
bccc4bb62b3a9a531f96e25345817728c0374b46ba1b16280e0450f2e7ba95ae  NDO_JFz_Row13.olean
2128278e9052bbed2796004f3f5a45fb813f5a9b5e2ab9a2254e89266b56fecc  NDO_JFz_Row14.olean
2727e6bdb34420227603823d9627908f264591657f05c01f04d4421adc5ff66d  NDO_JFz_Row15.olean
39485e04e1d6a3ef0b3a59a045198b520936360086d10429674cec3913625960  NDO_JFz_Row16.olean
91639333ca96d5e6e8ff89c2b5fe84c0d6a071b0bf9d9afae36d2f1d062d6010  NDO_JFz_Row17.olean
59313bac92d0c18ca48db826be892c96152b5fb239799e88d7714134c2bffce7  NDO_JFz_Row18.olean
3c8f83e9871eac9cd9b3ba14beb1a6fe17e3e9f027ad0ceb6c33ae446e01d559  NDO_JFz_Row19.olean
002ee5cd090c463e32aaf73a8e26dde0cf4e3bb086e012f988a9426ae944d52e  NDO_JFz_Row20.olean
ed6dffaae41a8d0cbcdfce2048ef65f87589b6b22b3882e0e9f3b5b3770280d3  NDO_JFz_Row21.olean
9aa1aba84e91f79acf6e489eef41c1572d729fee4986b92888289b94b4130ebb  NDO_JFz_Row22.olean
96e173cc0f5aff7f2a27ff42f35e777ea8ada21162dd8003f62e692d97bb6216  NDO_JFz_Row23.olean
5ad94a91e1d4a5f7486037ca40d9e5511d0b4540944689d0a1432703b7c9a65c  NDO_JFz_Row24.olean
f926ae0315e65cd70c4404c9064706fe413a2ab94405ed9538b651e6aea5ab09  NDO_JFz_Row25.olean
e396a3cd6872a4a155d7f0e0eaa9fa2b5801cba143ce9911719ab6c292b44393  NDO_JFz_Row26.olean
7049f29e50f384db24c3ecbb578d90633552432a62697cb9cb4f760cf9ed49c2  NDO_JFz_RowGeometry.olean
89ae2dd9c38d12710af480277f9421aec1c500d2c305ebeef8cac0050eabeb43  NDO_JFz_Scan00.olean
a036a07edafb19af72e53dd848b9750e626b915911d126b03af4e861c30b7712  NDO_JFz_Scan01.olean
161058a620b78399656cebd4cc309f4c2fef3b26f5a1f028c25938112393dcad  NDO_JFz_Scan02.olean
13014944fcd6e75d886e0f6019f6f1d49ec9936ae279003251f3439f84cec23e  NDO_JFz_Scan03.olean
b214e21e1f5a3589583c412ffe6b67cb6110834c3fae34a4d161abbf9d58b9db  NDO_JFz_Scan04.olean
d40d6ce848da4389a8e77146372e39602e3ad00c393e430bab1b081b0d3bc1b8  NDO_JFz_Scan05.olean
5a6d87a2130003dc3a76bb53ae4e1f0167418bc60ed5eeb90065e2c6ecda7365  NDO_JFz_Scan06.olean
25527d8cb07cfa8de46d94a9e8d9de3e26224a520ee035b2712965993f0c71b2  NDO_JFz_Scan07.olean
4331036a9b9863d4197b68ef494eab83c393049f47e4bef874572af48ca95897  NDO_JFz_Scan08.olean
3f10df50faae8e8e0ecd96d393f2097fbabaadf01b14b915536418a0618d1a78  NDO_JFz_Scan09.olean
bcd8c723412b144a3ecf6cfcc2f638c2593d906bc3cef17b36bcb1a86327836b  NDO_JFz_Scan10.olean
fc9fdf895f447778b9336161759ce1f40ab38d8228c655841249af46e6f4797d  NDO_JFz_Scan11.olean
6404c0b289dbf04240faf749b1462ca285c9628ca263b011c0e8c4ce33215ffd  NDO_JFz_Scan12.olean
da2e96ee8dd2354019ad3c46b1b96427a19db32a6c8a8665ac04fd9a7e45b307  NDO_JFz_Scan13.olean
c0da58eb13632de896db41053552f808cd0451042c5d4d610d9b349e9d59f925  NDO_JFz_Scan14.olean
ef9331ecbc3c742520b2428ee072b074d640d81185c46c8d794b2384725dd78e  NDO_JFz_Scan15.olean
caa126b76ca0ada940a0e427f718e4f399c24ae98ce0f9a641b0399882e9df42  NDO_JFz_Scan16.olean
36b23322b1a86a1e43f667339b3b05a27c3355e14be60d7685bc732ea1b0ad2e  NDO_JFz_Scan17.olean
e03b0f7f61439901f6a008d34223f74ecaae708385478d0c0cc1f09b39d11c21  NDO_JFz_Scan18.olean
0b4b3d7609b5d270fe2b98293d8af609d2d70592f4a9f2b71b5bdc7f53fd2b11  NDO_JFz_Scan19.olean
748842279d00d50fe140c7f715d1b1f6168004bceddddff79015050d8e45b4e1  NDO_JFz_Scan20.olean
5c1ff5ef83f4d55c80734608f5533febe3bf34aa8fb52a9d6175e713cfca52ba  NDO_JFz_Scan21.olean
ac9fb2698deb877756ab026d95263a7b424175c3d1e8fbfa13df9dd883ceee76  NDO_JFz_Scan22.olean
28a263ba84684bb694eaaf3c1fae0ddeaa81f18614fb9865ae1ec5a88195b68c  NDO_JFz_Scan23.olean
eeab81e260cd25220100f8b207d17983fc68c165d954dfb7c900977c30e95fe0  NDO_JFz_Scan24.olean
1fb8c29cdeddf996dca662693bb924baf12a1f17aa5bcc1de2995ec5a938f2cd  NDO_JFz_Scan25.olean
efc108eb563843829c26630f3ab45190bb7b3c63047d052ba493c3d65305f604  NDO_JFz_Scan26.olean
b8d875ff2edef3cc816a7439b5242a948ba8f5b76db0f24907bcd4efc7244292  NDO_JFz_Scan27.olean
4f968c7c2be6087e4dda0c14c65b09bcf08f70d078d1fe335d3247548e291555  NDO_JFz_Scan28.olean
b8d2656c8fb4b8efcb9ab367ff4a718b7b4f7ffd3ee33c6acad69719f7a4acfe  NDO_JFz_Scan29.olean
3137f45c5c7fbee171c4ad76e97330f92f0306232a1941e235f6d2d3845b9569  NDO_JFz_Scan30.olean
39f04dcfbaa1807a981e582c68bfc15c53eb1cd025251646e270c4f8212628d3  NDO_JFz_Scan31.olean
dcb5fb957822a3e1bde2de57ec9605a92723c4a6820a3127a1e947dcb2c7befe  NDO_JFz_Scan32.olean
7e4e84aedce2c9729d15a5080182439a32d9adc186947575ea75281eb20ec75d  NDO_JFz_Scan33.olean
8dbbe5498a8b68a4de33b9a948acbfb1356d05191d335b0313aeef2d0bd97913  NDO_JFz_Scan34.olean
a21035709f52ae8aa1d93d0adea1278c76a34c98db2b6997a9689f026db766e1  NDO_JFz_Scan35.olean
bfa8fb275e294c7f2025c2932c6999f01eaadc220d0b5e0d70cb4a64d07af019  NDO_JFz_Scan36.olean
6bb437b550975f6f3e538d3344d385f2f20c18adc7b792ec3b041269830fe3ed  NDO_JFz_Scan37.olean
41a88923df999c2279ee59234e384bc1752443da2502a2dbe7548c6dae10a199  NDO_JFz_Scan38.olean
39e2aec4e93941c009972baf3ce29aaea50a81798f4b474fcb9dbb36add94ab0  NDO_JFz_Scan39.olean
a054167c11d6d93dedb0b7cbcd056c17980d0c723000cc9889f2663425d0b427  NDO_JFz_Scan40.olean
4d7596a593b0b584f23ec1bcf79ff49a66fd42fb1a934b62f674584a01fc77c4  NDO_JFz_Scan41.olean
32e1e824503e975d070c5bd52a6e44710c5ff2a7ed02672324f670ea00051ff3  NDO_JFz_Scan42.olean
e9f50d275d95fe9690832e94ef779f6cd660ef5a549acd5badf884fb4c24486f  NDO_JFz_Scan43.olean
666737dd639b888887eccef3ac6267a96d8fcd5fed1a9a1d3edab4f563c57bca  NDO_JFz_Scan44.olean
7d9032d1911641e071031c9862960235c7a7548608b6811b74208eb7725d6178  NDO_JFz_Scan45.olean
a5ecb0c3d0b17e1c65277f7f2720dff3baccc45d352bda95c38d06b6dd80b0de  NDO_JFz_Scan46.olean
7fb128e19f4606fa45bbc428aeaeb206ccb103304994126e45f4b1470ff452b3  NDO_JFz_Scan47.olean
89c3a9e7d7e5a355673f0829f3e55d458e6a2822271227836e4c172a27cedb67  NDO_JFz_Scan48.olean
a09657871f2d0e656617108c470933701bb042185834924d786818b2f6cefffb  NDO_JFz_Scan49.olean
5a4f728b3d1555f24b8f32156264e318b9b7178dc9d7731d59bdfca6fe0cae3f  NDO_JFz_Scan50.olean
cbdcfc8b687694db81ab425540e9f06f6c9af0948e1fff30dea8ac1d68f8bac4  NDO_JFz_Scan51.olean
52e4e85481417f1d5fe9dbc24a8b9ace93dde48ecb90c379a9307179247e225d  NDO_JFz_Scan52.olean
48ef768e9c8d852bf5d23baa0cb704f478a7a78490698b703a5619ff785a7b3c  NDO_JFz_Scan53.olean
10d75a4c7de674c30da31ac1b3b203d9eb92dc97ed755984f62629fb7a562007  NDO_JFz_Scan54.olean
afcda36e4832b665017d66914be67d6275b6cd6f1b97a1a14f17056a86e7060f  NDO_JFz_Scan55.olean
f0329c2b3e4aaf62e7a8f2e48bab5c529aaacd997c010e9ad0a6ea40453b8640  NDO_JFz_Scan56.olean
d46219b014b6a202f2682a20e6ad48c826cb74f5291caccabeffc356e40bf34a  NDO_JFz_Scan57.olean
4b4c15e7e1a270446790a0978ad771bb1fabfb1c9bebc70e4c7dc890904d2138  NDO_JFz_Scan58.olean
749e4af4dde8c4ef94ee1d7c033907fc9fdb4332987c08d155e43e11acbba352  NDO_JFz_Scan59.olean
98851cb1af4b80f3ebabceaef3e043bcd7aecc49dfe57fe44b2d6f1b5914f79f  RPz8_JFx_DataCheckpoint00.olean
8a9dfd2698c1353255b1e64b46f33e65e54353a4b0dd5f84a57c736853b5845d  RPz8_JFx_DataProof00.olean
d85b450bc30de64043161efdf944a8922df5303c66b8ff45c76b6f374a123944  RPz8_JFx_DataProof01.olean
b78e829dea7afcfaf46a64036ea95cebc9df31ee93d0606eb1b08b5f67f3ca38  RPz8_JFx_DataProof02.olean
175867de24d491507bc212db5583b6d7011fa6fb032e55bca6096312b1c6a0f5  RPz8_JFx_DataProof03.olean
7e39f96b9d14e909c64499a04f9465fd481acaecfa0e272124e9fdbc9da26213  RPz8_JFx_DataProof04.olean
31785dd3e05238789af0d0e1721a0fc5df3618f46e8a37ba55d9cac03c0b1749  RPz8_JFx_DataProof05.olean
3ff888eddf25773f3bfe676822c189167d7130843f107608ba2bd84e66d60fea  RPz8_JFx_DataProof06.olean
2e6e4226cb3b3110efd64d6a603a6b5185e13b5b984102633f7dd4645415b4d6  RPz8_JFx_DataProof07.olean
c003f58251826c7bcf5b17ed27517de56dc2ef8e674ad8f466a9c5a5b4544e96  RPz8_JFx_DataProof08.olean
1f89cd007ab15d997dfe7a4879b9cd11cfc8b6c336a9c03b308b88065a106b93  RPz8_JFx_DataProof09.olean
0a2d80b92431a8c9685f22cbd537164c5871e4a1e995374bf9f085b2aee81ff3  RPz8_JFx_DataProof10.olean
d8b3b469d0cc9fb9bc1cf00b6b200cb1f711867dbb2def185d9d3d7fae8a8e31  RPz8_JFx_DataProof11.olean
8bb9144413c2a877e7956632bccc863c813ee6e4c724d5c61dd62a3ebf1d7efc  RPz8_JFx_DataProof12.olean
b94a6722510e2d685bcf4b89891ff5b69a58a0cf2f4c9cd5a438d96a00360fb3  RPz8_JFx_DataProof13.olean
35e8ffe6a0c19c342d5ef981a8bb5fe7ed9d5a961a6f3e3c1b652f3c80c80f73  RPz8_JFx_DataPublic00.olean
326e511d0004d6e8a30b8da046c1b76793b91a1e39bde38a1ec2314252b0b606  RPz8_JFx_NativeBytes.olean
```

## 12. Files

- `PIN2W4_inputs.py`, `INPUTS.json`, `inputs/` (PIN2 transfer and withdrawal proof, statement, checkpoint, public bytes and frame; `inputs/SHA256SUMS`)
- `PIN2W4_regen.py` (check and PIN2 modes; data, scan, row, record and statement generators), `PIN2W4_sha.py`, `generators/` (patched copies), `REGEN.json`, `SHA.json`, `PIN2_*.json` (regenerated generator manifests)
- `sources/` (every source whose text changed, under its release module name)
- `PIN2W4_compile.sh`, `PIN2W4_drive.py`, `PIN2W4_ready.py`, `PIN2W4_sha_compile.sh`, `drive_status.tsv`, `logs/`
- `PIN2W4_crosscheck.py`, `CROSSCHECK.json`, `OVERLAY-PIN2-W4.sha256`

target not yet established
