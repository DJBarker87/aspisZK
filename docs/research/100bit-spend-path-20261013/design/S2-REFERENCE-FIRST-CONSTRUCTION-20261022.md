# S2 fixed-initial reference construction

S2/S1/S6 and the per-attempt target remain OPEN. No enclosing actual-native
accepted-run premise is claimed discharged by this packet. This is the
reference-first construction route after the native-first pairing's original
input-frame obstruction; no production change or source adoption is requested.

## Checked complete-reference restoration

`S2SdkReferenceFirstReuseV1.restore_checkpoint_buffers` consumes an ordinary
return of the COMPLETE installed borrowed reference, the original account2
read, and the original checkpoint-vector read. It derives

```
(buffers out).set checkpointAccount.data_slot.val original = buffers initial
```

for BOTH Ok and Err statuses. No independent buffer frame, child success,
whole-stage totality or arbitrary chosen proof/public snapshot is assumed.
Successful execution's exact CP-only image and complete rejected execution's
all-buffer frame are reused, with the same checkpoint account and original
read. `returned_other_read` additionally derives exact unchanged vector reads,
including invalid-slot behavior, away from the checkpoint slot.

Before, using a native-first pair to construct a fixed-initial reference
witness required identifying post-native proof/public allocations with their
original contents. Reference-first execution can instead use the checked
complete reference frames to recover the original input buffers before native
execution. The new theorem proves that recovery step; it does NOT itself
prove that the full reordered native/reference pair corresponds, or remove
the actual-native enclosing theorem's remaining premises.

## Forward source acquisition construction

`S2SdkReadyAcquireV1.checkpoint_success` constructs the actual complete
checkpoint-helper result from its successful source cell read and zero
counter. `shared_success` constructs the successful shared-helper result
from its source read and `shared_allowed` observation. The checked increment
and actual next counter/state are derived, including isize::MAX-1; SDK/helper
success and final state are conclusions, not premises.

`S2SdkReadyStateV1` instantiates these on the existing full OwnedSdk and
OwnedDataCell types with three cells. Accounts, lamports, bytes, counters and
Rc fields are retained as arbitrary typed values. Actual slots2/1/0 are
constructed separately, to be consumed at the original source sites: public
after scanning, proof after decode/validate/encode. No reordered execution,
new simplified carrier, opaque SDK replacement or enclosing caller success is
asserted. These are prerequisites for the forward complete caller constructor,
which is still required. Native-to-owned representation and actual primitive
helper interpretation remain external; these lemmas do not disguise them as
cryptographic assumptions.

## Validation and exact pins

Source: `lean-candidates/s126-caller-boundary-20261021/`.
Accepted targets and exact source receipts:
`evidence/s126-current-caller-20261021/accepted-targets.json`.
Exact transitive imports/object hashes (no binaries):
`reference-first-reuse-import-pins.json`. Current source parent a70eb93074;
source/command/tool hashes are recorded per target. The adopted source overlay
remains25866ec331cc7ce27dd9956609c11d32fa8fa58a/S4adoption29cbab431742f7e899870595167efa193a379f0a;
no historical transitive proof is silently attributed to adopted S4 bodies.

| Target / accepted attempt | Exit | Wall s | RSS bytes | Swap | Axiom reports |
|---|---:|---:|---:|---:|---:|
|S2SdkReferenceFirstReuseV1 / v4|0|14.651516958|3303882752|0|4|
|S2SdkReadyAcquireV1 / v3|0|16.187168833|3221733376|0|2|
|S2SdkReadyStateV1 / v2|0|22.681650500|3256418304|0|6|

All twelve reports are subsets of propext/Classical.choice/Quot.sound. Atomic
local lock, -j1 -M4400, smallest changed module first, warm dependencies, no
unchanged full replay. Excluded drafts retain their exact errors and compiler
recovery axioms; none is accepted evidence. Draft corrections concern Vec
observation/representative substitution and a reserved binder name, not changes
to theorem scope, quantifiers or the security target.

## Excluded full-pair attempt

`prepare-sdk-reference-first-native-pair.py` constructs the complete reference
from original unseeded buffers and metadata BEFORE native execution. Proof and
public vectors move rather than clone; only original1768-byte CP is cloned and
restored. Then the complete original native SDK/copy/implicit-cleanup body runs.
The same full statement and source child ports remain; no SDK/copy/Drop stub.

Codegen passed: exit0,1.987s,595428KiB RSS,swap0. The paired query timed out in
SSA conversion: exit1,188.432s,6516064KiB RSS,swap0. This is NOT equivalence
proof and receives no proof credit. Fresh admission, optimized Rust flags,
6G/8G/MemorySwapMax0, one job; no unchanged retry or raised cap. Source-only
packet `sdk-reference-first-native/` includes exact sources, inputs, tool pins,
receipts and failed case logs, and no binaries. Its manifest hashes were
checked. Earlier complete native-first success pairing remains valid within
its original qualified domain; it is not invalidated by this timeout.

## Exact remaining enclosing obligations and next deliverable

The next deliverable is the forward COMPLETE installed caller constructor,
using the actual source instruction/key/metadata guards, the same initial
SDK byte vectors, actual scan/decoder/validator/encoder observations, the
same first result, original stage1 write and finalizer. Reuse the checked
`reference-first-v3` Rust constructor and `S2FirstEntryNormalizationV1`;
do not rebuild or re-prove their unchanged parsing/gate results. Existing
`ExtractedTerminalEquality` has the needed symbolic array eq/ne laws;
reuse those for key/owner guards instead of normalizing32-byte arrays.

The actual frozen SDK accepted-control/first-entry facts and that constructor
must be instantiated together. Original-input identity at native reached calls,
exact native output account frame, general runtime/ABI/allocator/P6 and ordered
source child/oracle interpretations remain explicit. The lead14-field interface
also needs checkpoint writer/account/TX2 reader and public retention or
reconstruction; cross-TX hash equality alone is not byte identity. S6 actual
caller decoded reuse and S1 original Prepared/claim challenge trace then consume
that caller connection, with their remaining totality and adopted-source re-pin
obligations. No source/protocol decision has been made here and no permission
request is needed for the next proof work.
