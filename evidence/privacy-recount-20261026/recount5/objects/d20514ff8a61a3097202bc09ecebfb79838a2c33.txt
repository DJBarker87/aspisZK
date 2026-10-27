# Library row table

Candidate source callback laws supplied: **7 → 8** (V177/V178/V179/V180/V181/V182/V185/V186), through `PV_CBL_CallbackBundle`. Native P6 bounds and the distinct extraction/Kani toolchains remain explicit. The canonical recount and endpoint are not edited here; RunJoin/deployment integration remains open. Target not yet established.

| op | row | route | status | theorem | crate/version; source hash | receipt |
|---|---|---|---|---|---|---|
| 205 | V231 | extraction | OPEN; escaping reference output requires loan validation; structured Drop requires destructor semantics | — | `sha2-0.10.9/src/core_api.rs` sha256 `73b160d98bfa6737688875ad73da5e3c2c93582604dc313d208200e12fdab676` | aeneas-source-op205-opt-frontier-01 |
| 208 | V232 | extraction | OPEN; x86 SHA-NI dispatcher loan/intrinsic boundary; owned fallback block value and totality proved; byte driver still open | PV_CBL_Op208Shape.extracted_shape (not source closure) | `sha2-0.10.9/src/core_api.rs` sha256 `73b160d98bfa6737688875ad73da5e3c2c93582604dc313d208200e12fdab676` | aeneas-source-sha-dispatch-opt-resume-dispatch-01; 43044/43081; SHA-BACKEND.md |
| 209 | V233 | P6 | OPEN; structured Drop requires destructor semantics | — | `block-buffer-0.10.4/src/sealed.rs` sha256 `9327ee3e567ae779b83c2b7f4f3ff56fcb2117163e023e7b0e37759e7e8d1f5c` | aeneas-source-op209-ref-opt-frontier-01 |
| 212 | V234 | extraction | OPEN; structured Drop requires destructor semantics | — | `digest-0.10.7/src/digest.rs` sha256 `8beab74640774c9f6811daa6dac9b5a8867f5beeb0b552a9b5ddbc5cfc196ed0` | aeneas-source-op212-opt-frontier-01 |
| 215 | V235 | extraction | OPEN; escaping reference output requires loan validation; structured Drop requires destructor semantics | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | aeneas-source-op215-opt-frontier-01 |
| 216 | V236 | extraction | OPEN; escaping reference output requires loan validation; structured Drop requires destructor semantics | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | aeneas-source-op216-opt-frontier-01 |
| 217 | V237 | extraction | OPEN; generic loan/Drop; concrete-default monomorphization has invalid UInt generics | — | `digest-0.10.7/src/core_api/wrapper.rs` sha256 `033777bed7d140b158e15d50fda8a6e06557ce89bd0738fcca692be2c39e8b8a` | aeneas-source-op217-opt-frontier-01; charon-source-op217-mono-resume-concrete-default-01 |
| 219 | V238 | extraction | OPEN; escaping reference output requires loan validation; structured Drop requires destructor semantics | — | `digest-0.10.7/src/core_api/ct_variable.rs` sha256 `703bd62fb693a437e319d1192988bd674f9127a6b76f73b4c58c71afc79bc013` | aeneas-source-op219-opt-frontier-01 |
| 25 | V177 | P6 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op25_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 39647/39648/39650; kani-pathbuf-borrows-r01 |
| 26 | V178 | P6 | SOURCE LAW SUPPLIED; checked UTF-8 carrier; native byte lengths0–2, every output coordinate | R1Z.PV_CBL_CallbackBundle.op26_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 52498/52499/52505; aeneas-source-join-slices-opt-resume9-verified-02; resume9-join-slices-two-r01 |
| 28 | V179 | P6 | SOURCE LAW SUPPLIED; P6 valid UTF-8 length 2, arbitrary byte index | R1Z.PV_CBL_CallbackBundle.op28_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 43000/43001/43004/43005; resume-string-path-01; route P6 |
| 29 | V180 | P6 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op29_source | `std/src/path.rs` sha256 `14fd41348e74555af61dacf60bd78edc9cd2ea534abdad3266854a9a0b696886` | 39647/39648/39650; kani-pathbuf-borrows-r01 |
| 30 | V181 | P6 | SOURCE LAW SUPPLIED; empty-byte carrier adapter; native n≤4; allocation/deployed association retained | R1Z.PV_CBL_AppendBundle.op30_source | `alloc/src/string.rs` sha256 `d320cfe75e8962583e54f4094648a7d981684749f9eb65f46cceaedb1de8916d` | 41592/41594/41596; resume8-capacity-r01; op30-bytes-opt-resume8; earlier direct extraction rejected |
| 31 | V182 | P6 | SOURCE LAW SUPPLIED; extracted byte append and checked UTF-8 transport; native valid UTF-8 2+1 | R1Z.PV_CBL_AppendBundle.op31_source | `alloc/src/string.rs` sha256 `d320cfe75e8962583e54f4094648a7d981684749f9eb65f46cceaedb1de8916d` | resume8-push-r01; op31-bytes-opt-resume8; 41593/41642/41671/41681–41683 |
| 32 | V183 | native-effect deferral | DEFER(pv-runjoin): recoverable native allocation effects | NATIVE-EFFECTS.md | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | — |
| 33 | V184 | P6 | OPEN; Copy Slice/caller-output reference extracted, marker/empty laws checked; native u8 length0–2 passes; actual Word/prefix/native association retained | — | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 52503/52507; resume9-pop-slices-u8-r01; older rejected/timeout receipts retained |
| 34 | V185 | P6 | SOURCE LAW SUPPLIED; P6 bounded native check | R1Z.PV_CBL_CallbackBundle.op34_source | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 39604–39610; bundle 39622; kani-op34-exact-006 |
| 35 | V186 | P6 | SOURCE LAW SUPPLIED; native default check | R1Z.PV_CBL_CallbackBundle.op35_source | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 39611/39614/39622; kani-op35-exact-002 |
| 36 | V187 | P6 | OPEN; complete borrowed-Slice Result/identity-clone value law and QM31 adapter source bridge proved; native N=1024/owned/actual Clone association retained | PV_CBL_ArraySliceBridge.source (reference only) | `alloc/src/vec/mod.rs` sha256 `a9cfdfc0aeb91ccbe2e382784df6c6b4533dd07c7ed979f782069f784996729f` | 52500/52502/52506; aeneas-source-array-slice-result-opt-resume9-std-01; old rejected gates not rerun |

Std/alloc source corpus: rustc **1.98.0-nightly (14210df0e, 2026-05-31)**, toolchain nightly-2026-06-01. Kani gates use their separately pinned rustc **1.93.0-nightly (53732d5e0)**; no deployed std/ELF association is inferred. Cargo library rows use the versions in the file column. Full source SHA-256 values above are retained.

Resume 2026-10-27: supplied rows **4 → 5**, adding V179/op28 through `StringTypes`/`selectedString`; `op28_source_all` and the four `opN_source_string` laws coexist. All prior publication names persist. The native op28 gate covers valid UTF-8 strings of length 2 and arbitrary byte index; no unbounded or deployed-toolchain association is inferred. Final audits: 43098, 43099, 43100; all standard axioms only. Full resume metrics: RESUME-RECEIPTS.json. SHA-BACKEND.md names the exact dispatched/foreign symbols and the fallback-only scope.

Third pass: op30 uses an extracted safe empty-byte reference and a checked
empty-only String representation adapter. Native P6 proves contents agree
and capacity≥request for n≤4. This adds a bounded candidate value law, not
allocation-effect, deployed-toolchain, endpoint, or side-channel closure.
Op31 safe borrowed byte append extracted with no external template; its
String representation transport is now kernel checked. Op33 borrowed extraction passes
but calls missing `Vec.remove`; 41588 is rejected and gives no row credit.
Op26 and op36 loan frontiers, and op32 allocator-effect deferral, remain.

Third-pass publication: `PV_CBL_AppendBundle` supplies all seven laws together.
V182/op31 composes the exact extracted safe byte append with kernel-checked
UInt8/U8 and UTF-8 representation transport. The native link covers valid
UTF-8 initial length2 / tail length1, all byte values and complete equality.
Encoded strings outside the usize carrier fail explicitly; invalid result
bytes fail decoding; size-overflow, fail and divergence are not erased.
Rust's valid-UTF-8/source-image, allocator/world, separate toolchain and
unbounded deployed association remain explicit P6 limits. No canonical
endpoint/deployment premise is removed by this candidate publication.

Final third-pass audits:41797/41798/41799, all exit0 and standard axioms only.
Current publication: `PV_CBL_AppendBundle`; full soft block source theorem:
`PV_CBL_SoftBlockSource.source`. No digest row or endpoint closure is inferred.

Fourth pass checkpoint: candidate rows **7 → 7**. Extraction route now proves
complete fixed padding contents, both one/two-block branches, exact retained
first buffer and reset position in `PV_CBL_PadContentSource.source` (52430).
This closes the owned-reference content gap, not native loan/callback/Drop
semantics of V231/V233. Byte codecs extract with no external template;
source-to-byte-value and sixteen-lane composition are in progress. No SHA-NI
refinement or shipped change is made. New pass tally: TALLY-resume9.json.

Fourth pass second checkpoint: **7 → 7**, route extraction for supporting
SHA reference facts. `PV_CBL_ByteWordsSource.source` (52448) proves all sixteen
big-endian decoder lanes together; `PV_CBL_SoftByteSource.source` (52449)
composes them with the complete extracted soft block on arbitrary byte block
and state. No V232 dispatcher or V231–V238 wrapper credit is inferred.
The last accepted own modules remain below 2.7 million KiB RSS, swap zero.
Finalization/reference upload is admission-gated; no timed-out arithmetic
Kani gate, local Lean compile, SHA-NI refinement or production edit ran.

Fourth pass third checkpoint: **7 → 7**. `PV_CBL_FinalizeSoftValue.source`
(52466) proves the complete extracted fixed owned soft finalizer result on
arbitrary state/block counter/buffer and pos<64. It composes canonical soft
compression, padding contents/order, the exact length expression and all 32
output bytes, retaining the first padding buffer and reset position zero.
`PV_CBL_FinalizeSoftTotal.total/no_fail` (52467) preserve full Result outcomes.
`PV_CBL_DigestBytesList.list` (52459) identifies output bytes with the ordered
flattening of the eight big-endian words. Forty identical extracted helpers
were reused and four new definitions checked (52450), with no external leaf.
Actual borrowed generic wrappers/Drop/dispatcher and deployed association
remain OPEN: no V231–V238 row credit or endpoint removal is inferred.

Fourth pass buffer checkpoint: **7 → 7**. The extracted complete fixed driver
is kernel checked (52471), as are its exact default/constructor state (52474),
mutable-array loan leaf (52473), byte transition including full-block counter
increment and reset (52479), eager invariant (52482), loop unfolding (52483),
and arbitrary sized-Slice update totality (52484). The content-fold and
whole-digest composition checks remain pending admission. This is no credit
for borrowed digest Update/default/finalize wrappers V231–V238. No native
wrapper/dispatcher/Drop or deployment premise is hidden in the dictionary.

Fourth pass soft-reference composition: **7 → 7**. The complete extracted
owned fixed SHA-256 digest is now proved against a deterministic value model
for every sized byte Slice: `PV_CBL_DigestSoftSource.source` (52497).
`PV_CBL_DigestUpdateSource.source` (52490) identifies the buffer update with
its byte fold; deterministic padding/finalization are checked at 52494/52495.
Whole digest totality is checked at 52492. No concrete SHA recurrence is
normalized again. Native generic wrapper loan/Drop semantics, runtime
SHA-NI/soft dispatch, compiler/toolchain/deployed association and native
allocation/world/side-channel closure remain separate P obligations; no
V231–V238 row credit or privacy endpoint removal is claimed.

Fourth-pass publication: candidate supplied rows **7 → 8**, adding V178/op26
through `PV_CBL_CallbackBundle.op26_source` (52505). The new dictionary calls
the supplied generic AsRef instance and preserves its Result, then uses the
extracted caller-output byte reference and checked UTF-8 adapter. Its native
P6 link covers byte inputs of lengths0–2 and every output coordinate; arbitrary
native PathBuf/UTF-8 image, allocation/world, unbounded and deployed association
remain explicit. The prior seven names persist, and the final selection audit
checks that they coexist on selectedJoin. No canonical endpoint is edited.

V184/op33 remains OPEN: the changed Copy Slice reference extracts and the
marker/empty laws check, plus a new u8 length0–2 native gate. No full actual
Result<Word,Error> prefix/payload/native association is inferred. V187/op36
remains OPEN: the complete generic Result wrapper and identity-clone value law
now bind the previous QM31 value adapter through a checked source theorem;
actual native Clone, owned/error Vec, allocator and N=1024 success association
remain. op32's native allocator-effect deferral is unchanged. All four new
Kani gates pass, with no old pop/array timeout gate rerun.
