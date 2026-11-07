# NMM unresolved native steps

Target not yet established. No protocol counterexample or row closure is claimed.

## TX2:217

K032 proves the complete returning-Err branch at original768 arbitrary bytes,
with havoced typed replies, exact argument records and immutable input frame.
K033's returning-Ok payload window timed out90s. Earlier whole-result,
all-Ok, byte/pointer-log, row/word-window and changed-solver shapes are retained
and retired (K002/K003/K006/K011–K014/K027/K028). No cap or timeout was raised.
The next changed shape is success-to-21-Ok-replies coverage plus a typed all-Ok
reply branch. Both must be gated; an accepted-only relation is never a row root.

Pinned Kani's loop_invariant macro accepts while loops only; the frozen loop
is a for loop. Exact source/hash/excerpt: NMM_TOOL_BOUNDARIES.json. No compiler
or macro patch, for-to-while source rewrite, or copied-fragment producer is
substituted for the actual frozen parent.

## TX2:234

K017–K026 validate finite data-error plumbing in V1/V2, not whole234. The
selected Custom reply with an Ok input byte vector is excluded by the CLOSED
data law on composition; it must not be reported as an actual data-error run.
K030 whole legacy and K031 legacy argument-window shapes timed out90s. Both
are retired. A changed first-PDA-error branch is prepared.

Legacy PDA calls carry master_account.key() and admit a harness-local record
through that retained pointer. V2's second call instead receives only local
registry-program bytes, a copied bump and local loader program; no retained
harness context reaches that signature. The missing deliverable is an exact
argument/reply record for this call, without writable statics, provenance
forgery, writes through shared key bytes, a frozen-source change or new trust.
No deterministic PDA surrogate or Rust callee-law assumption is used.

## TX2:233

The full value transcription and four-payload carrier compile. Native233
waits for gated217/234 candidate laws, as the job requires. Pure allocator and
cleanup bookkeeping is outside the obligations under(bl); it is not a blocker.
No post-abort heap or cleanup state is invented.
