# ProverRwResumeP6 concrete contract design

Entry: 1097f5bef9f0ae52ac0c4df61857dc0d16e9bc26. Prospective only.
No crates/programs, installed registry, toolchain or existing candidate edits.
No premise of output equivalence, no new OS law, no source adoption.

## Contract and immutable carriers

Reuse FactoryState's complete prospective source, including actual Request::draw,
Draw::resume and native driver. Rename only its private FactoryState prefix to
ProverRwResumeP6; record exact spans and hashes before execution. Public method
before/after remains nonce32 -> Result<Secrets,Error>. Selected contract remains:
Draw { Request { nonce32, retry:usize }, Zeroizing<[u8;64]>,
       Result<(),getrandom::Error> }
 -> (Control { More(Request) | Done }, Result<Option<Secrets>,Error>).
The nonce32 and initialized postbuffer64 are unrestricted, entry ranges0..15,
and both primitive outcomes are unrestricted. A safe cfg(kani)-only associated
constructor in an immutable getrandom0.3.4 copy receives NonZeroI32 and constructs
Self(code) directly on host x86_64 Linux. This covers its full valid representation,
including non-OS positive errors and i32::MIN; no unsafe construction or orphan
Arbitrary implementation. Production source and dependency identity stay pinned.

## Actual cleanup observation (separate proof target)

Keep the original Zeroizing Drop's self.0.zeroize(), actual array/iterator/scalar
Zeroize operations, volatile writes and fence. No destructor stub or suppression.
In an immutable job-owned zeroize1.8.1 copy, add cfg(kani) metadata-only snapshot
methods, then hooks immediately before/after the original Drop statement. Safe
shared references observe only the live payload at those hooks. Scalar u8
observation is typed; array observation indexes elements, with no padding/layout
assumption. No pointer escapes a hook, and no read follows a completed Drop.

An event's fresh ordinal identifies that actual invocation, its length and the
payload snapshots. The source hook's borrow identifies valid storage for that
invocation only; it does not identify an earlier moved-from allocation or prove
native provenance. Do not invent persistent addresses/owner IDs across moves.
Expected event payload/order: Err gives only64; success gives64 before result
inspection, leaves both32 owners live, then explicit returned-owner disposal
separately gives field32 then leaf32; rejection/exhaustion gives leaf32, field32,
64, each once. Rejection increments retry before lexical Drop in actual source.
If equal payloads prevent source-role identification, retain that identity gap;
equal bytes must not be claimed to prove owner identity.

## Erasure and admissibility obligations

A byte-exact transformation manifest can check that removing the named cfg(kani)
additions recovers upstream source. That is syntactic association ONLY. A semantic
relation must additionally establish that ghost writes do not change payload,
result/control, moves, public frame, panic/termination or original Drop execution;
that metadata cannot overflow/panic/alias/re-enter; and that reads occur during a
valid borrow. Kani assertions check its instrumented memory model, not a native
Rust aliasing/provenance theorem. Do not promote source erasure checks or leaf
zeroize evidence to a mechanized semantic erasure proof. Keep this gap explicit
if existing P6 does not supply a producer. No cleanup-closure claim without it.

## Native boundary, ranking and error world

The prospective Request::draw source must still initialize freshzero64 and call
literal getrandom::fill once, then move its actual bytes and outcome into Draw.
A Kani fill stub is ONLY the existing64 primitive boundary: arbitrary initialized
postbuffer, Ok/Err and arbitrary provider ledger state outside Result. Native
world W is distinct from Request/control and a ghost ledger. Checking the stub's
ledger survives Err is bookkeeping transport, not OS-world refinement. No law
for partial errors, independence, freshness or retry uniformity is introduced.
A native primitive-outcome/ordered-event producer and experiment transport must
associate this call to literal ProverCommitPublicNonce40.E1's contextual
successful64 law. E1 alone does not establish the source association.

Start must prove zero nonce -> no draw and nonzero -> retry0. Resume's local
contract covers arbitrary entry0..15, but the actual driver invariant remains
an obligation: entry equals prior rejected draws, nonce preserved, entry<16,
and each rejection increases it once. Do not compose finite16 by assuming a
whole-resume theorem. Native driver/outer8 arbitrary mutable public policy,
durable ledger, complete error observations/full transcript, E1/L1/L2/L3,
selected client and source-artifact gates remain open unless separately proved.

## Execution discipline and carried budgets

Commit this design before execution. Prefer one new Kani check for unrestricted
normal native draw/resume control plus honest Drop observations; at most two,
reserve last of60. Entry Kani57/60, Lean236/260, extraction54/56, backend15/16,
Rust checks/tests0/3, ELFcommands0/3. No extraction/backend invocation justified
by the known014 blocker. No full invariant/BMC or manifest. New Kani scope is
High3GiB/Max4GiB/Swap0/Tasks64, optimized compilation followed by one symbolic
draw/resume and actual destructors. Existing timeout240s unchanged. Before/go
use the unchanged corrected FactoryState all-hierarchy scanner with requested4G
before and0 at go, finite caps+new strictly<55GiB, exclusive uncapped resident
plus7GiB OS/control reserve; fail closed. One denial ends launch attempts.
Do independent source work after denial. Pin sources/packages, dependencies,
compiler/sysroot/binaries before/go; retain command, revision, exit, wall, RSS,
swap and axioms N/A, failed originals and actual invocations separately.

No production edit before the concrete source/effect proof. All three current
ELF gates, fixedcoin1000/identical proof bytes/native refinement/events/E1/
L1/L2/L3/selectedclient/quiet median<15s and <=10% slowdown remain adoption gates.
Both deployed targets not yet established.
