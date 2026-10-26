# Stage 3: prefix isolation and non-vacuity

KANI023's arbitrary80-byte instruction / symbolic-flag ASDI prefixes timed out
for both checkpoint sizes. No unchanged rerun is made. The prefix slices are
literal source spans, recorded by byte offset and SHA in PoolN_prefix-manifest.
Replacement restricts the instruction to an encoder-produced canonical fixture
and keeps arbitrary checkpoint data and metadata flags. This is an explicitly
weaker fixture class, not arbitrary-dispatch closure; it supplies concrete
reachability evidence and a smaller rejecting-guard predecessor.

KANI024 failed to compile because the new forest fixture used an unimported vec
macro. KANI032 repairs that source to alloc::vec; it is not a resource retry.
The Rust errors, timeouts and original source snapshots are retained.

LEAN008 now passes the two shape-consistency theorems, using an explicit cons
head and List.length_replicate rewrite. LEAN006/007's broad simp attempted to
normalize replicate and failed at default recursion depth; both are rejected.
No recursion/heartbeat/memory limit was raised. These consistency theorems are
not native handler-reachability theorems; native cover results remain separate.

The full dispatch/alternate-role/source-effects conjunction is not established.
No theorem named PoolN_Frame.all_handlers is fabricated from the guard matrix.
The remaining Kani budget is used for concrete prefix, CPI and stack gates,
followed by a precise remaining-obligation handoff.
