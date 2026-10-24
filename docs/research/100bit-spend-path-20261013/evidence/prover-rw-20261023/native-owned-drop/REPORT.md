# Actual owned byte Drop: source component evidence, unadopted

Branch codex/cx-prover-rw-20261023; base b724680f271cf989d7acef38d7438e4df1138c78.
Design committed before execution as588db5d759. The manager revoked the old
blanket Guard prerequisite; no old failure or tool acceptance status changed.
No shipped source, installed tool, protocol, feature, wire, verifier, security
contract, wallet/chain, trust, merge, push or adoption change. Both deployed
targets remain **not yet established**.

## Exact established component and limits

For N=32 and64, six new universal Kani checks execute unchanged registry
zeroize1.8.1 code, not a destructor stub or Zeroize axiom.045/046 prove actual
array Zeroize yields all zero bytes from arbitrary initialized bytes.047/048
call actual Zeroizing destructor once in retained storage and observe all
payload bytes zero; these initial pointer observations are Kani-memory-model
only and are superseded for the Rust lifetime argument by049/050. The latter
MOVE an actual Zeroizing owner into a helper, compute the inner payload offset
while live, invoke drop_in_place once, reacquire a fresh root byte pointer from
live MaybeUninit backing storage, and prove zero payload plus unchanged two
arbitrary16-byte frame arrays. Extra pointer checks and unwinding assertions
are enabled; no memory/safety/unwind check is disabled. Each size is universal
over its bytes/frame, not a fixture and not arbitrary generic Z/policy coverage.

Rust memory argument: MaybeUninit is initialized with a complete valid owner.
No layout or repr(transparent) assumption: a live dereference finds the inner
array; offset_from uses pointers into the same allocated object and the harness
checks offset+N within owner size. Only the integer offset crosses destruction.
All live reference borrows end before drop_in_place. The pinned destructor
calls array Zeroize, whose iterator visits actual u8s and writes default zero
with volatile_write plus compiler_fence; neither u8 nor its array owns any
allocation/Drop implementation. Backing frame storage remains alive and is
used afterward; fresh raw byte reads observe ONLY these initialized payload
bytes, never padding or a reference to the dropped owner. No old child pointer
is reused, no freed allocation is accessed, no live owner is forgotten, and
MaybeUninit prevents a second automatic destruction. This is a source safety
argument plus Kani checks, not a mechanized Rust aliasing/provenance theorem.
No promise is made to wipe old moved/copied storage, registers or caches.

Kani warns that atomic_singlethreadfence is treated sequentially. Unsupported
caller_location/foreign constructs are reported globally and verification
would fail if reached. All checks pass with those checks enabled. Thus the
claim is source-level sequential physical payload/frame behavior under Kani,
not native reference testing, concurrency, volatile instruction preservation,
L3 hardware erasure, whole-source trace, or a kernel-checked Lean theorem.
No runtime/native reference tests were run in this step.

## Actual extraction obstruction and exact source path

Charon045 exposes all foreign bodies;047 narrows to explicit zeroize bodies
without extract-opaque-bodies, preserving source unchanged. Actual Drop,
array Zeroize, IterMut Zeroize, volatile_write and atomic_fence have structured
bodies in focused LLBC. Aeneas046/048 use unchanged candidate014, explicitly
-eval-drops with pinned Config/Main guard, and both reject BEFORE emission:
"escaping reference output requires loan validation; unsupported Drop shape".
No Lean helper is available to compile or audit, so no Lean attempt was spent.
source-audit.json expands hashconsed types and retains complete signatures,
calls, precise Drop statements and spans. Actual core::slice::iter::IterMut
Iterator::next (function105) returns Option<&mut T>; necessary iterator loans
are distinct from the old nested swap Guard. Precise generated Zeroizing glue
also contains projected/trait Drop (function6), outside014's local+regular
structured-glue acceptance. Do not weaken that guard or accept candidate015.

These are concrete failures of the two actual entrypoints' generic dependency
graph. A fully monomorphized32/64 graph was NOT tested; these failures do not
prove every possible concrete-only lowering impossible. No source/printer
patch or remaining backend build was spent. A narrow Kani/P6 source-helper
route now has actual destructor evidence; its Lean binding and integration
with emitted glue remain unproduced, not an opaque-zeroization axiom or a new
AeneasExtraction trust grant. Old Guard regression remains failed/unaccepted.

selected64-source-audit.json pins actual generate_for_mask_nonce: invalid
nonce has no draw;16 iterations, initialized64, partial-error fill followed by
? cleanup, two32 copies, success MOVES32 owners and discards64, failed test
cleans leaf32/field32/64, final repeated-zero error. Universal payload checks
cover possible partial-write contents, but DO NOT prove actual error/glue/drop
invocation order or owner/event transport. Normal Err and unwind integration,
returned owner lifetime, generic captures and escaping refs stay open.
RealR1's mutable adaptive FnMut proof_account remains unrestricted; provider
and durable store advancement on Err plus ordered draws/errors/retries/ledger
and publication events remain required. No new entropy prototype was started.

## Validation, evidence identity and remaining budget

ledger.json retains exact commands, source/dependency/compiler hashes, flags,
exit, wall, peak RSS, swap and N/A axioms for all new non-Lean results. All six
Kani checks pass (1.621-4.658s; maximum203564KiB; swap0). Charon045/047 pass
(0.725/0.279s); Aeneas046/048 reject (0.420/0.231s). Each launch passed full
hierarchy admission before reservation and at go under6G/8G/noSwap/Tasks64;
largest populated reservation34.375GiB. No OOM, cap raise, shared lock/tool
edit, unchanged proof replay or full manifest. No Lean output means no new
#print axioms, imports audit or Lean theorem claim; every receipt says N/A.

Postrun read-only audit002 adds missing Charon/cargo/time/timeout executable
hashes to audit001; it does not retrospectively repair absent preflight binary
pins. Kani verifier/compiler and Aeneas binary pins were checked before/go.
source-assessment.json explicitly distinguishes those postrun hashes, the
historical design revision label, per-file source identity and reused old
candidate014 evidence. Kani generated artifact hashes/sizes only are retained,
not binaries. The9,025,816-byte broad LLBC stays on host (see exact size/hash
in ProverRwOwnedDrop-large-input.json; authoritative size is that JSON);
focused LLBC is retained. No derived JSON over5MB is committed.

Before/after every existing native/refinement/E1 theorem is identical. No
assumption discharged from whole-owner/privacy claims, added or concealed.
New byte-component checks use existing Kani/P6 tool semantics; no opaque
Zeroize axiom or extra extraction trust. Actual source-helper Lean binding,
normal error/move glue/trace transport and unwinding remain open. Current
f8c0ec72/63ad3e9c/121f3e29 ELF pins are unchanged targets, NOT newly validated.

Cumulative budgets (all failures charged): backend15/16 (1 available,
unspent); extraction48/48 (0); Lean236/260 (24); Kani50/60 (10). This step
uses6/8 permitted Kani (2 remain within step),0/4 Rust test/check commands;
two optimized Charon Cargo source-extraction commands are charged separately
as extraction045/047. No further extraction is allocated. The next producer
must bind this actual destructor relation at existing P6 to supported
caller/glue source, then preserve normal failures, unwind and ordered owner
and policy events. A concrete-only monomorphized preflight remains untested;
requesting or spending a new allocation is a lead decision. No new entropy
prototype over that unresolved integration was made. Literal E1 conditional64,
OS primitive,16-inner/8-outer and native owner/event transport, L1/L2/L3 and
all adoption gates remain unchanged.
