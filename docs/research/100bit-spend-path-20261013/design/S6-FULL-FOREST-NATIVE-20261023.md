# S6 full-forest native boundaries

Status: actual native semantic getter checked; full codec roundtrip, actual
stage1 caller binding and S6 remain OPEN. No frozen source or ELF changed.

The native `PoolV1PairForestTerminalStatementV1::semantic_public` was checked
against the complete original native statement/payment/transition types at
source freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a. For BOTH variants it
returns references to the SAME payment payload and SAME complete
`common.lane_transition` object. Pointer identity covers every payment field,
live-snapshot field, frontier, candidate root and candidate frontier; there is
no abbreviated public carrier, chosen field subset or canonicality restriction.
The source function is pure match/projection; no child stub was used. The
arbitrary payload construction uses only the original integer/array structs;
no enum discriminant, pointer, reference or Box is fabricated. The statement
enum is constructed normally. This is native source evidence for the getter,
not a construction of the native/owned execution relation or a codec result.

`s6-native-semantic-projection-v1`: native Kani0.67, exit0, wall1.099s,
peak133972KiB RSS, swap0; all20 checks and both variant covers pass.
MemoryHigh6GiB / MemoryMax8GiB / MemorySwapMax0 / TasksMax64, fresh admission.
Rust code generation uses explicit opt-level3, MIR0, overflow checks enabled
(the Cargo development-profile label does not override recorded RUSTFLAGS).
No Lean theorem ran, so #print axioms is N/A. The source-only packet retains
exact source/tool/lock/command/feature configuration and every active local
source inventory, checked unchanged after the gate. The library feature is r0;
this is not a release ELF reproduction. Read-only audit:
`python3 tools/s6-full-forest-roundtrip-20261023/check.py`.

An initial unstubbed gate called the full native ASF8 decoder and encoder on
arbitrary1880-byte input and checked a symbolic byte in the common/header144
region, with covers for accepted transfer/withdrawal. It timed out during
verification: `s6-native-full-forest-header-v1`, exit1, wall188.249s,
peak6496732KiB RSS, swap0, same6/8GiB/Swap0 cap. It establishes NOTHING about
roundtrip, safety or accepted coverage. Source, exact failure and postchecks
are retained under `s6-full-forest-native/excluded-header-timeout`. It was not
rerun unchanged or with a larger cap.

The next route is source extraction of the complete actual outer encoder,
with validation and nested lane/payment/digest codecs as EXPLICIT children.
An initial Charon/Aeneas attempt returned status0 but inspection found only
the wrapper, with the entire outer encoder external. This is excluded evidence,
not extraction of the desired source body. The wrapper-only attempt is retained;
the inclusion list is being corrected. The raw generated axiom templates and
resource options are diagnostic material only and must not be imported.

Remaining S6 obligations are unchanged: actual full1880-byte encoder/decoder
composition, both variants and ALL fields/header/reserved bytes, actual
allocation/error/effect behavior, native-to-owned relation and stage1 caller
binding, same decoded statement through first/first_decoded/adapter, and
actual installed tx1/None/ordered runtime children. A getter check neither
removes FullForestAcceptedRoundtrip nor supplies S2CallerFacts.

## Current source models and kernel results

The corrected include list extracts the ACTUAL complete outer encoder and
current boxed decoder. Constructor naming conflicts were resolved only in
LLBC backend-name metadata. Original names, function IDs, types and bodies
are identical after removing those metadata rename fields; both JSON source
ASTs are retained and checked. This does not alter Rust source or semantics.

`S6FullForestCodecNativeV1` retains all complete statement/error carriers and
all outer control/byte operations. Exactly nine nested functions become
explicit Ops fields: digest encode/decode, forest validation, late encode/decode,
transfer encode/decode, withdrawal encode/decode. They are NOT imported axioms,
and no whole encoder/decoder is opaque. Raw generated templates/resource
options are diagnostic only, never imported. These definitions compiling is
source-model feasibility, not a roundtrip or actual SDK execution theorem.

Actual new source/control claims:

- `S6FullForestCodecRangesV1.statement_bytes`: the emitted size expression is
  TOTAL and equals1880.
- `decode_wrong_length`: every non1880-byte input returns the original
  WrongLength, for arbitrary children. `decode_success_length` derives1880
  from the same accepted source-model decode. No decoder child success or
  length witness is a premise.
- `S6FullForestCodecEncoderControlV1.encoder_control`: complete Result
  factorization into the actual validator and VERBATIM remaining source body,
  including outer fail/div and inner Err. `encoder_rejects` preserves the
  validator error; `encoder_success_validates` derives validator success from
  that same encoder execution. No child implementation is thereby discharged.
- `S6ForestArrayWritesV1.copyRange_total`: TOTAL native-emitted
  index_mut/copy/back sequence under its actual interval and source-width
  bounds, with the exact full-array update/frame as a conclusion.
- `S6ByteInverseV1.toLE_fromLE`, `u32_to_from`, `u64_to_from`: symbolic complete
  byte inverses, without canonicality premises, enumeration or huge reduction.
- `S6RetainedDigestTotalV1.encode_total`: TOTAL complete unrolled digest
  reference, with no source-child success or canonicality premise. The old
  source module was absent from warm caches; only its exact two digest
  definitions were materialized as `S6DigestReferenceV1`, retaining the full
  eight-limb/32-byte carrier. The Rust reference matches the native checked
  reference after only function visibility/name and local identifier renaming.

All changed targets were compiled individually first, atomic local lock,
Lean4.32.0, -j1 -M4400, zero swap. Accepted receipts and source/tool/direct import
pins are in accepted-targets.json; `s6-full-forest-current-import-pins.json`
pins the transitive object hashes, with no objects distributed. The eleven
focused targets have24 standard-only definition/theorem audit reports. This
is not a coherent final release replay. Failures remain excluded evidence.

## Native loop/reference checks

These gates use complete original native carriers; no opaque output stub or
reduced semantic statement replaces the target. The only replacement in the
frontier checks is the EXACT concrete digest reference already checked equal
to the actual native encoder for every eight-limb native value. The runner
refuses to launch unless that predecessor passed, every native library source
inventory matches it, and the reference bytes are identical.

| Native target | Exit | Wall seconds | Peak RSS KiB | Scope |
| --- | ---: | ---: | ---: | --- |
| s6-native-digest-encoder-v2 | 0 | 1.984 | 269708 | Original digest loop equals unrolled reference, all native8-limb inputs;191 checks |
| s6-native-digest-roundtrip-v1 | 0 | 2.176 | 274700 | Actual accepted32-byte decode/encode identity;392 checks, both accept/reject covers |
| s6-native-frontier-loop-v1 | 0 | 31.292 | 1000572 | Actual snapshot foreach equals20 explicit writes; complete native Snapshot, arbitrary800-byte initial frame and every position;195 checks |
| s6-native-afterstate-loop-v1 | 0 | 30.482 | 989608 | Actual afterstate foreach equals20 explicit writes on its complete native carrier and688-byte array frame |

Swap0 throughout; fresh6/8GiB/SwapMax0/Tasks64 admissions, MIR0/opt3 and
unwinding assertions enabled. Native source proof, not a Lean axioms audit:
#print axioms is N/A. Every command/tool/source/lock pin and failure remains
in the source-only packets. Source freeze is25866ec331cc7ce27dd9956609c11d32fa8fa58a;
the inherited host receipt's workspace revision is not silently substituted
for this source freeze or the explicit candidate file hashes.

Full-loop frame claims above concern those EXACT reachable caller-sized frames,
not standalone serializers for arbitrary slice lengths. Surrounding original
validation/header/error source is unchanged. Complete context/native runtime
transport, allocator/abort effects and SDK/account framing are still open.

## Excluded attempts and continuing work

A checked-contract instrumentation attempt for the tiny digest encoder timed
out (exit1,186.409s,6554372KiB,swap0). It is NEVER used as a verified contract.
The equivalent concrete implementation is used instead. The ordinary-stub
parent first hit a contract-closure codegen error in the shared cache; a fresh
isolated pure-mode cache compiled but still timed out (exit1,192.833s,
6507500KiB,swap0). Neither establishes any header/roundtrip result. No cap was
raised or unchanged large proof repeated. Future contract/pure jobs need
separate codegen caches; this does not diagnose a shipped SDK bug. Kani contract
use/check semantics are documented in the [primary Kani contract documentation](https://model-checking.github.io/kani/crates/doc/kani/contracts/index.html).

Full source extraction with all codec bodies included reached three concrete
borrow-join failures in sequence: original digest loop, original snapshot
frontier loop after the checked digest replacement, original afterstate
frontier loop after both checked replacements. Source, logs, exact errors,
Charon/Aeneas pins, wall/RSS/swap and LLBC hashes are retained in
s6-full-forest-exploration. These are EXCLUDED attempts, not proofs. Isolated
extraction references use only the exact checked unrolled fragments; actual
production remains unchanged. Whole contextual equivalence and adoption/source/
artifact re-pin obligations stay explicit. The next extraction incorporates
the now-checked afterstate loop reference, then the complete source roundtrip
must be composed and installed into the actual caller.

Remaining is still the complete FullForestAcceptedRoundtrip instance, all
nested source child instances, current decoder/encoder/runtime joins, actual
first/first_decoded/adapter stage1 connection and S2 native observation. These
results do not construct S2CallerFacts or establish the100-bit target.
