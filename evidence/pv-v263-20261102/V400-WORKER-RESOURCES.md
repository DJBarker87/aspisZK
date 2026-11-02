# V400-257 — rdea-2 resource failure independence remains OPEN

This is a named P obligation, not a fourth TrustItems field. The relevant
frozen source is 9c131667ca00f4daae78da6299b09a9fe0d00da9, with deployed
r1p-check + ct-host-prover, public-work-trace OFF, Rust 1.94.1 release,
panic=abort. Existing source/feature receipts remain authoritative.

Exact target: take two executions in the fixed ActualPhase/capture family
with the SAME public input and coupled public OS/runtime initial state and
answer policy, allowing different witnesses and witness-derived operands.
Their resource request histories (operation, thread, count, layout, requested
bytes, alignment, stack size, and request-time observer information), OS
failure/denial answers and failure/abort observations including D159 timing
must agree, or have the required equal coupled distribution. Proving only
item counts or returned vectors does not discharge this target.

The new Lean `PV_V263_PublicRequests.V400Obligation` exposes the deterministic
three-step interface (requests, answers, observed failure timing). It is not
instantiated for actual executions, nor assumed at the privacy endpoint.
`same_public` proves only congruence of source-capacity shapes; it does not
prove actual paired executions supply equal Shape values.

## V400-257-entry (OPEN)

Prove the sequence of reached map invocations, their stages/counts, and the
entry ACTIVE TLS flags agree for paired actual runs. Source calls use
stage=200,count=27 then 2 for C1/C2; sumcheck uses stage=100+r and
count=28*2^(9-r), r<10. Establish that validation, callback errors and preceding
resource failures cannot make these invocation histories witness-dependent.
For each nonnested call force=true bypasses the small-n shortcut, so exactly
15 spawn requests are issued on the no-failure path, even n=0. Nested calls
issue zero spawns. Thread-denial prefixes may be shorter than 15.

## V400-257-layout (OPEN)

Prove actual T/F layouts are determined by the reached public instantiation:
Result<Word,r0::Error> for commitment and Result<QM31,r1_wire::Error> for
sumcheck. A witness-dependent Word enum tag does not change Rust's type layout,
but a native layout/size receipt is still needed. Bind the two range layers:
outer n=16 gives one family per thread; original n gives width(n,k) elements.
`PV_V263_Range` supplies arithmetic/overflow bounds for these capacities.
`PublicRequests.capacities` is a capacity-site census in merge order, NOT the
actual time-ordered allocation syscall trace. Its handlesPush length is not
Vec's actual growth capacity. `bytes` is element payload, not headers/rounding.

## V400-257-lowering (OPEN)

Bind rust-src 1.94.1/deployed std allocation request counts and sizes for:
handles Vec::new and every push/growth, caught-result Vec capacity16, outer
pool output capacity16, each one-family collect, inner item Vec capacities,
final host_work output capacity n, appends, frees/drop glue and scope records.
Include zero-size/zero-capacity specialisations, Layout overflow/abort paths,
allocator rounding, thread packet/JoinHandle storage, default stack allocation
and RUST_MIN_STACK/environment, TLS initialisation/destruction and diagnostics.
Thread primitive answers may fail; no world is assumed to grant resources in
the privacy result. The grant world is only an existential resource witness.

## V400-257-callback (OPEN)

Prove complete request-size/count laws for the actual callback cones, including
encode_commitment_lane and SemanticOracle.evaluate/evaluate_assignment with
the exact op227 bridge. Callback Rust Err is a vector VALUE and does not cancel
other callbacks; panic/abort is separate and can truncate the request history.
No pure fixed callback, successful vector, constant oracle or callback-success
endpoint premise replaces this obligation.

## V400-257-answer/timing (OPEN)

Prove resource answer policy and coupled public initial runtime state have no
secret channel, including TLS history, live task slots, allocator state,
addresses/errno subsequently read, scheduler decisions, joins, panic payloads,
hook/stderr formatting and panic=abort. Even equal request counts/sizes do not
alone prove equal failure TIMING when worker duration/interleaving can vary
with operands. Establish that duration/scheduling law for the full D159
observer, or retain it here. No observer or simulator change is made.

## What has been discharged

Only symbolic public-shape congruence and the thread-request projection:
`Team.fifteen` derives fifteen handles in a stateful grant world;
`Team.deny_first` retains first-spawn denial with its event and no source
Result projection. Range bounds and source-order index coverage are already
accepted. None is an actual capture witness or full native resource law.
V370 compiler preservation and D381/D386 compiler-cohort obligations remain.
