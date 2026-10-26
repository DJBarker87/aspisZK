# S6 native boxed-decoder wrapper — 26 October 2026

The actual frozen thin decoder wrapper now has a complete **relative native
result/field certificate**, including its SDK error mapping and returned-box
semantic references. This does not close S6 or any enclosing SDK-source premise.

The release ledger at research `21cd42575bc0058b44a7cde0f2723c6ad2b269c5` still pins compiler source
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. The tested signature and complete
body of `decode_public_statement_box` are byte-identical to
`programs/r1-cost-probe/src/r1_pool_adapter.rs` at that freeze. The isolated
fixture uses the exact native statement, common/payment/lane structures and
native FormatError hierarchy. Its ProgramError is the actual
solana-program-error2.2.2 type re-exported by frozen solana-program2.3.0;
that re-export and every resolved package checksum are pinned.

## Established source-tool claim

For every1880-byte input, every initialized typed native decoder return
`Result<Statement,FormatError>` and the default Kani normal-allocation model:

- The wrapper invokes that decoder once, with the SAME input pointer/length.
- Every native decoder error maps to the SDK's InvalidAccountData.
- A successful statement is boxed with the same variant and EVERY native field.
- The actual semantic_public getter borrows the payment and lane transition
  from that SAME returned native Box. The native Box destructor runs after use.

Exactly the decoder return is cut. Neither the wrapper result nor its Box,
getter, map_err, error type, returned statement or field operations is replaced
by an opaque reply or simplified carrier. The arbitrary decoder reply is
independent of the arbitrary bytes, so the certificate covers every actual
normal-return correlation, without assuming successful/canonical decoding.
The native decoder's internal execution is not proved by this cut.

All three covers (decoder error and both successful statement variants) hold
in every family. Inputs and all statement scalar coordinates are independent.
Seven native error enums have proof-only Arbitrary derives; stripping those
attributes restores every original declaration/body. Production files are
unchanged. Fixture manifests remove only dev/test declarations. All52 resolved
registry versions/checksums match the release Cargo.lock, and their source
files were checked against the checksum-verified crate archives. Original
SDK error layout and variants, including its owned String variant, are retained.

## Complete field coverage and validation

One unrestricted field observer was too expensive. The final observer has
24 transfer /25 withdrawal field families, with unrestricted native usize
indices modulo each array dimension. The generator expands every family and
checks exact agreement with all608 transfer /633 withdrawal scalar coordinates,
including the variant tag, all byte bindings, u64 sequences, raw M31 coordinates,
and BOTH20-digest frontiers. No field or scalar input is omitted or canonicalized.
Primitive widening to u64 is injective; equality of all families/indices gives
full native value equality. There is no array-of-independent-child-success
hypothesis or independently selected output statement.

All25 Linux family targets are green, on the SAME source/tool/import pins:
`proofs::native_boxed_decoder_family_0` through `_24`.
They passed **19225 assertions**,3/3 covers per target,
maximum verify wall 69.971415001s,
maximum process RSS 1262856KiB, zero swaps.
Sum of verify-phase wall times is 764.499087756s;
this is measured validation time, not a protocol cost bound.
Every job used one optimized build job, MemoryMax2GiB, High1792MiB,
MemorySwapMax0, checked unwinding and default Rust/Kani safety checks.

A distinct aarch64/darwin negative control changes only the final common
candidate-frontier word in the expected statement. Exactly its scalar assertion
fails (1/769 failed,3/3 covers),75.147676166s/2936815616B peak process RSS,
zero swap,4GiB local aggregate watchdog. It does NOT fill any Linux positive
family or establish a cross-target release replay. The unmodified positive
claims above are entirely Linux checks. An earlier local compile-only
predecessor passed11.144851750s/606257152B/zero swap and is not a proof result.

The source-only packet retains exact native inputs, candidate proof sources,
source/function/package/tool/sysroot/import pins, every command/status/time/RSS,
swap, cgroup peaks/events, admissions, covers, failed attempts and controls.
No binaries, GOTO, LLBC or ELF artifacts are included. #print axioms: N/A(Kani);
no Lean axiom, sorry, native_decide or resource-option override is added.
Normal malloc success/no-uninit-check interpretation remains explicit.

## Failed attempts and resource decisions

- Source-only package preflight first expected .cargo-checksum.json files not
  present in the local cache. It now validates actual package sources against
  archive hashes in the immutable release lock, without compiling or downloading.
- v1 NUC metadata chose stable rustc and rejected nightly flags; v2 pins rustc
  explicitly but its fresh admission failed. No compiler/solver ran there.
- v3 metadata passed but a runner reuse guard wrongly expected an old compiler
  receipt. The guard was fixed before native compilation; source unchanged.
- v4/v5 whole targets timed out during goto-instrument preprocessing, before
  Checking harness or any CBMC result. The first field observer had633 arms;
  source factoring reduced that to field families and removed a large Option
  from the fixture reply mechanism, retaining the COMPLETE native Result.
- Inspection identified ensure-one-backedge-per-target on the1880-call input
  constructor. Splitting independent bytes into58x32+24-byte constructor chunks
  preserves ALL1880 byte coordinates. The previously stalled pass then completed
  in0.794s. The body under verification and native decoder interface did not change.
- v6 reached CBMC but timed out at120s on the unrestricted family selector.
  The final25 constant-family targets retain the exact complete projection.
  Their field/array indices remain universally symbolic, and the finite family
  union is audited. No native parser was replaced or re-proved.
- A planned live soft-threshold adjustment found v5 already terminal; its
  resource-review.json says changed=false. The final source-split jobs explicitly
  launch High1792MiB within the SAME2GiB hard cap. No OOM or swap-killed job was
  rerun unchanged at a larger hard cap.
- After families0..13 passed, fresh admissions denied family14 before launch.
  No passing target was rerun. Pending14..24 used the owner's more-memory
  authorisation: a5GiB physical OS/remote reserve, PLUS the independent
  MemAvailable >= all unused finite-cap headroom+4GiB test, rather than the old
  9GiB reserve. Hard job caps and all other jobs' limits stayed unchanged.
- The same pinned native build workspace/cache was reused. Only our fixture
  source and binding changed, after old scopes were verified inactive and all
  before/after hashes checked. Native crate bodies and other sessions were untouched.

## Enclosing obligations remain explicit

Before/after enclosing signatures are unchanged: **zero enclosing premises
removed**. In particular, the published SDK consumer still requires
`S2W_DigestExtraction.AeneasExtraction (ClaimsUnrolledSdk.sdkOps ...) native1 native2 hashv`,
SDK borrow/runtime admission and actual library/allocator/source association.
The parsing/codec TOTAL and1880-byte inverse proofs are existing checked Lean
results, reused rather than re-proved; they are not themselves a native heap
execution certificate. This packet supplies the native wrapper's result/field
and same-object getter part of that connection.

Still needed for L176: native decoder/model execution association, initializedness,
allocation failure/abort and its internal ownership/cleanup/effects; then composition
into the SAME actual SDK execution. The wrapper's own normal Box creation/drop
runs here, but does not settle those whole-decoder or SDK effects. L179 belongs
to the S2 library/native caller owner; source-to-frozen-ELF lowering is L186/S10.
No allocation-model assumption is relabelled as a cryptographic assumption.

No source adoption or production change is requested. Any future source candidate
needs explicit equivalence/adoption and affected source/tool/import/artifact re-pins.
S1's source-model preparation/canonicality/data proofs are now with the lead SAP
owner and were not duplicated here. The previous native Prepared/claim sampler
and query certificates retain their arithmetic/dot/scan and SDK/runtime boundaries.

**Whole S1/S2/S6 and the per-attempt <=2^-100 target are not established.**
No grinding/work-normalisation credit or numerical contract change is used.

Audit: `python3 tools/s6-native-box-wrapper-20261026/check.py` (PASS).
Evidence: `evidence/s126-current-caller-20261021/s6-native-box-wrapper-terminal-v1/`
and `s6-native-box-wrapper-audit-v1.json`. Source-only final audit exit0,
3.269090s, maximum child RSS 44761088B, swaps 0; no compiler,
solver, extraction, Lean replay, source re-freeze, wallet or transaction operation.
