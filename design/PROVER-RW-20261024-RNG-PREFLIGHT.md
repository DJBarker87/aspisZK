# Explicit entropy provider preflight

Base: 71100fccbd960c13cc43ba03fd4aacf39e510b34, H5 already merged.
Authority: LOG D187 and D191; no adoption, backend patch or verifier change.
Design committed before prototype/source work.

## Minimal interface and retained boundary

Current source: `StateOnlyAttemptSecrets::generate_for_mask_nonce` in
`crates/aspis-prover/src/state_only_entropy.rs`, lines 211–238. It checks the
nonce, allocates a freshly zeroed Zeroizing 64-byte buffer per iteration,
calls getrandom::fill once, copies two private halves, checks both nonzero,
and retries at most sixteen times. OS failure returns immediately.

Proposed internal signature:
`generate_with<P: Draw64>(nonce: [u8;32], provider: P)
 -> (P, Result<Secrets, EntropyError>)`.
`Draw64::fill(self, bytes: &mut [u8;64]) -> (Self, Result<(), OsError>)`.
The updated provider is outside Result: failures must retain the advanced
state. This is an owned state, not a constant token. A concrete finite tape
owns its remaining replies; removing one reply distinguishes successive calls.
No second independent execution supplies the regression's successful draw.

Existing boundary: `ProverCommitPublicNonce40.E1` lines 44–47 specifies the
uniform law of each successful raw 64-byte OS return for every prior context.
`next`/`run` lines 22–38 separately carry the schedule, failed events and tape
cursor. E1 makes no law for OS errors and proves no extraction correspondence.
Native leaf remains exactly getrandom::fill on that fresh buffer. Its wrapper
must be associated with this same primitive boundary, retaining partial writes
on error and cleanup; a whole-owner equality is never a field or assumption.
An opaque wrapper is not by itself a proof of that association.

## Sequence and stop rule

First use an isolated, source-derived prototype under tools, with no native
candidate change. Extract its actual owned owner and finite-tape provider with
the pinned Charon/Aeneas executable. Check zero then nonzero using the emitted
owner, including returned state on failure. Bind all externals by qualified
source names plus body/signature hashes; never inherit op numbers.
Next prove a direct finite-tape owner/control theorem and same-event source
transport. Only then extend through RealR1_client's selected callback and
prove_masked_retrying_with. Provider state must survive all eight attempts,
body rejection, fatal entropy errors and duplicate durable reservation errors.
Do not introduce an OS counter that resets or loses failure state.

If native leaf association cannot be justified under E1 and existing extraction
trust, stop dependent source plumbing and record the exact missing decision.
Pure specialization is not world-to-emission correspondence.

## Impact inventory and gates

Prototype changes no crates/programs and invalidates no native artifact.
A later entropy source change invalidates the old entropy/caller LLBC and
ProverRw* source-bound equations, external dictionary installations, E1 adapter
and L1/L2 joins; unchanged arithmetic and retained obstruction/effect evidence
remain historical with exact source assessment. New extraction closure includes
the actual provider, entropy owner, callback and retry owner. Native integration
requires current source/body hashes, same statuses/bytes and complete draw/event
history (zero, OS errors, cap16, outer cap8, rejects, duplicate reservations),
relevant existing differential gates, one final all-three-ELF rebuild against
f8c0/63ad/121f pins, coherent H5 interleaved performance <=10% slowdown, and quiet
host absolute <15s. PID2095724 is peer z3 and is never stopped.

Budget starts at 84/100 Lean and 42/60 Kani used: 16 and 18 remain; IDs11289–11399
require collision checks. Preserve 5G/7G Lean caps; Rust/extraction 6G/8G/no swap,
Tasks64, reservations below55GiB. No full frozen manifest without lead approval.
