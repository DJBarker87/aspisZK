# NMB cut table (in progress)

Target not yet established. No full native row credit or promotion.

| Cut | Frozen source | Contract / assertion | Control | Verdict |
|---|---|---|---|---|
| 344-owned-error-boundary | r1_pool_adapter_owned.rs:447–460 | ACTUAL stage1 contract, modifies empty, all original descriptors retained; arbitrary selected byte of key/owner/flags/length/byte-availability/program/instruction at the owned-child call returned unchanged through ProgramError::Custom | SAME harness under NMB_invert, pending positive verdict | K001 TIMEOUT124 / no credit |

K001 is a changed full-payload/aliasing shape, not NLQ's narrow checkpoint-window oracle. All three physical buffers and admitted snapshot payloads use Kani exact_vec with independent arbitrary bytes at58295/1880/1768. Snapshot's entire owned payload is unconstrained, never zero-filled. Plain snapshot and stage1_owned stubs are cut-point overapproximations, not stub_verified contracts on Ref or ProgramResult. The callback transports one arbitrary selected descriptor coordinate through its return value, with no writable static, Option<fn>, or global observer. Full snapshot byte equality is supplied by CLOSED343 at composition; K001 alone does not assert it. The malformed-length complement and every other segment remain open.

The strict source validator removes exactly two cfg(kani) stage1 annotations plus the recorded cfg-only harness-module suffixes, then hashes EVERY frozen source byte. Shared gate/launcher infrastructure is unchanged. Full resolved offline graph and pre/post frozen lock hashes are checked for every native scope. Exact canonical KMX files and patch bytes are validated. No field multiplication or SHA is unwound.

K002 is a RESOURCE DIAGNOSTIC, not a full parent segment certificate: source array assembly with one arbitrary58295-byte Vec, observed at one arbitrary offset. CBMC timed out90s (scope94.292281257s,3319820KiB,swap0); frozen offline graph and unchanged lock pass. No matched control or row credit. The full-vector construction shape is retired; next native work must split the source operation into a true window or another independent stretch.

Planned replacement of the retired actual-stage1 shape: SDK flags are transiently writable under their NLF law, so the Err-boundary contract's modifies set must name exactly the three admitted RefCell flag addresses (duplicates allowed), rather than be empty. Postconditions must be pure: raw read-only SDK length/flag observations replace data_len() inside the ensures expression. The flag observer is the same pinned representation observation as NLF's native receipts; no Ref/RefMut is fabricated. All three flag restorations are asserted. No replacement result exists yet.

## Final local-native cut inventory

These tests compile source-fragment copies in the scratch cfg(kani) module. They do **not** certify segments inside an invocation of the ACTUAL frozen parent. Thus every parent row's (bg)(2)(b) production obligation remains OPEN. K001 is the only actual-parent attempt and timed out; its empty modifies draft is invalid for transient SDK flags and superseded.

| Cut | Source line | Segment contract | Matched control | Verdict |
|---|---|---|---|---|
| stage1 guard | owned.rs:448 | exact data/count Bool, empty modifies | K022 inverted result | K021 PASS / K022 semantic FAIL; fragment only |
| snapshot0 arguments | owned.rs:452 | exact original occurrence0 and 58295/58295 | K024 wrong index | K023 PASS / K024 FAIL; fragment only |
| snapshot1 arguments | owned.rs:453 | occurrence1 and 1880/1880 | K026 wrong index | K025 PASS / K026 FAIL; fragment only |
| snapshot2 arguments | owned.rs:454 | occurrence2 and 1768/1768 | K028 wrong index | K027 PASS / K028 FAIL; fragment only |
| owned array assembly | owned.rs:451–455 | full metadata, length Ok, bytes tag, pointer/length/capacity; empty modifies over OLD regions | K031 inverted header; K032 old byte write caught by assignability | K030 PASS / K031–032 FAIL; full arbitrary58295/1880/1768 inputs; fragment only |
| exact deferred error supplement | owned.rs:451–455 | error variant InvalidAccountData retained | K034 fails INNER header contract before desired assertion | K033 positive observed, NO independently controlled exact-error credit |
| owned refs0/1/2 | owned.rs:380–382 | exact account reference selection, empty modifies | K036 wrong proof ref | K035 PASS / K036 FAIL; fragment only |
| checked proof extent | owned.rs:404 | checked addition, overflow tag and error | K038 inverted success predicate | K037 PASS / K038 FAIL; arbitrary usize operands; fragment only |
| admission/dispatch | lib.rs + adapter process | admitted TX1 exact bytes, route1 | K040 wrong route | K039 PASS / K040 FAIL; fragment only |

K004–018 are input-generator interface calibration, not shipped-function credit. At each fixed array size58295/1880/1768: inverted ensures fails; real-body zero assertion passes; unimplied zero assertion fails under stub_verified; outside-frame mutation is detected. NMB_INPUT_FIDELITY.json records all fifteen prerequisites. The helper starts from initialized storage and then permits arbitrary bytes; no zero-filled payload oracle is used.

K019/K029 compile errors and K003 unsupported intrinsic are findings, not passes. K002/K020 timeouts are retired; no larger cap/time was used. Every run records the exact frozen graph, offline resolution, lock pre/post equality, deployed features and canonical KMX SHA bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No multiplication, SHA unwind, uncalibrated contract shape or Option<fn> credit.
