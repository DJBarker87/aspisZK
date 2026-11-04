# D583 — stack resource boundary and public entry depth

Resume `28b62b77fc`, branch `codex/pv-evh-20261029`. Applies ruling
(rdea-2') from pv-common: residence is a stateful world resource answer;
stack exhaustion remains observable failure. Evidence class: **source and
binary-structural (adopted binary), plus Linux OS-model and V370 compiler-cohort**.
This is a structural proof and operational specification, not an elaborated
Lean runtime instance or a machine proof of the compiler/OS.

## Corrected physical arithmetic

Reuse the adopted `da36d6aa...` binary, PHYSICAL-D581's frame reservations,
and immutable `out-N91601.log`. The D581 prose and its checker incorrectly
reported entropy sp = caller c - 240: 240 counts only sub232 and the return
address, omitting SIX saved-register pushes (48 bytes). Correctly:

* entropy sp = c - (8 + 48 + 232) = c - 288;
* incoming mask = c+16 = sp+304, extent [sp+304,sp+336);
* helper Result = c+64 = sp+352; its 97 initialized bytes end at sp+449
  (= c+161), still inside the caller's 264-byte reservation;
* [sp,sp+232) and all entropy-local slots in PHYSICAL-D581 are unchanged.

D581's `entropy_sp_relative_to_retry_sp=-240`, mask256 and result304 are
superseded. Its checker PASS did not validate the six pushes in that equation.
Historical files/receipts remain immutable; this correction has precedence.
No accepted Lean theorem with those caller offsets is given new proof credit.
The actual mask/Result correspondence must use the corrected offsets.

## Public bound — proof on the fixed entry control spine

Let k be the argument to retry_attempt. At plan's call, k=0 (0x527b1).
The only self-call is 0x5cb20. Source prover.rs:635..651 permits it only
on Rejected, with k+1; binary 0x5c9ff increments rbp once and 0x5cb18
passes that increment. The entry guard 0x5c9ac..0x5c9b6 admits the callback
only for k<=7; k>=8 returns AttemptsExhausted before entropy. Induction:
initial retry activation has k=0 and one live retry frame; after j recursive
edges, k=j and j+1 retry frames are live. A prefix at entropy initializer
therefore has 0<=k<8 and at most EIGHT retry frames. A terminal cap check
may have NINE frames (k=8), but never calls entropy. Success, other errors,
faults and resource failure cannot add recursive edges. The proof is valid
for every choice of rejection/entropy/world answers; no successful suffix
or witness condition is used. The public bound is ATTEMPT_CAP=8.

The callback is inlined. Entropy's retry is a backedge, not a recursive call:
0x1458e1 increments its counter, 0x1458e4 compares with 16, 0x1458f1
returns to the same initializer. Its invariant starts at zero; entered
iterations are 0..15. Thus 16 entropy attempts do NOT multiply live frames.
EINTR/partial getrandom loops likewise do not grow this user call spine.
The public maximum number of initializer visits is 8*16=128, with possibly
unbounded syscall retries at a fixed depth. No entropy success is assumed.

Each retry activation, measured from its caller's baseline rsp, consumes
16 outgoing argument bytes + 8 return + 48 saved + 264 local = 336 bytes.
The first plan call and recursive calls have the same two argument pushes.
The transient adjustment around prove_masked_attempt is restored by
0x5cae3 BEFORE recursion. Let p be plan post-prologue rsp. At an entropy
initializer:

    sp = p - 336*(k+1) - 288;  k < 8.
    p - sp <= 2976.

Plan's own frame is 48 + 0x52a8 = 21208 bytes below plan entry rsp.
Therefore the active spine's pre-initializer displacement from plan entry
rsp is at most 24184 bytes. The ninth retry cap-check displacement is
24232 bytes. At the initializer, depth below plan is <=9 calls (eight
retry activations plus entropy); including plan there are <=10 activations.
All constants are public binary frame sizes; subtraction is interpreted
only on the granted, nonwrapping machine branch, never as a permission probe.

These are bounds on the named active entry spine. They do not claim a whole
client maximum stack footprint: older caller frames, completed intervening
prover calls, signal frames, kernel stack, and other threads retain their
own resource transitions. The 32-byte zeroize leaf on earlier entropy loop
iterations temporarily adds its call return address; it is absent at the
initializer. No global V400 or whole-client timing theorem follows merely
from this local upper bound. Rejection timing and resource requests in other
callees retain their existing obligations.

## World semantics under (rdea-2')

At a frame reservation/first access, the SAME process world answers a stack
request carrying actual thread/activation, current rsp, fixed extent and its
public stack limit. It advances mapping/resource state and ordered events:

    answer(world, request) = granted(world', current RW interval)
                           | exhausted(world', fault/abort prefix).

`granted` supplies actual nonwrapping interval residence under Linux RW
stack policy, permitted demand growth included. It does not create a fresh
abstract owner or identify a Vec. `exhausted` preserves guard/probe faults,
SIGSEGV/abort and timing; it never executes an initialized secret continuation
or emits fake entropy success. A hardware subtraction can precede a later
fault: the resource transition covers reservation plus its access outcome,
not a claim that SUB itself probes all bytes. A prefix waiting at the
initializer can still have a pending failure; it is not discarded.

This replaces D582's extra demand to prove current-VMA coverage independently
of resource answers. A granted world is a legitimate non-emptiness candidate,
but not an actual-domain witness until the full advancing execution is built.
Both answers remain in the run family. There is no adequacy premise, no new
T field, no always-grant callback and no domain restricted by future success.
The bounded public entry spine above discharges this spine's requested
public-depth bound under (rdea-2'); answers must still be coupled through the
same world, retaining existing V400 obligations for the complete execution.

## Exactly OWNER-conditional frame interface

Use D580's SAME base/heap/box/ops binders and fixed actual-prefix domain.
The complete branch-valued target is specified in FRAME-ENTRY-D583.md.
On a granted branch, ABI arithmetic gives alignment; the world resource
answer gives nonwrap/residence/writability; shared OWNER gives existing
heap/live exclusions. Thus OWNER_actual_prefix (pv-evhB4, after lead merge)
is the sole outstanding interpretation dependency of that structural frame
interface. It must not contain stack adequacy or assume a granted world.

The old unconditional writable assertion cannot also apply to exhausted
answers. D583 explicitly changes its conclusion to a branch result, retaining
all input prefixes. This is the authorized resource modelling change, not
an unreported successful-only filter. No implementation of the missing actual
carrier or OWNER, and no Lean actual_frame_entry proof, is claimed here.
