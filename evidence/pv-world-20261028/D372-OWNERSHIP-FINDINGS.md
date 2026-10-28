# Reached ownership boundary

The new recursive source erasure is not yet a native lifetime/Drop proof.
The actual emitted `prover.publish_compact` includes the pure bindings
`let (o, _) := core.option.Option.take p.backend.c1` and the analogous c2
binding. Rust's take empties the owning field before later scope exit; the
returned Option value alone does not describe that ownership update. The
emission's Result does not include a destructor trace. These bindings must
therefore update an ownership environment in the sidecar interpretation,
before the final implicit drops. Treating every pure let as a native silent
ownership frame would be unjustified. No such native frame law is asserted.

The scoped Vec<u32> package describes a consumed buffer and its deallocation,
not a reusable handle. Two equal erased element lists need not be the same
allocation. Current pointer/capacity, local binding identity, move/take status,
and generation on address/descriptor reuse must be related to the actual
native activation. The same issue applies to Zeroizing arrays: the explicit
op130 write and their later implicit Drop are separate reached effects.

`PV_W_Ownership` supplies the slot-consumption invariant and once-only glue
model, with generation-tagged tokens. Its association to native locals and
scope/unwind exits is still P work; model uniqueness does not establish a
native ownership theorem. `PV_W_MemoryLift.reserve` sends the new header to
commit explicitly; it does not reconstruct capacity from the Vec's list.

This is a precise source/interpretation finding, not a counterexample to a
ROWS7 row or the privacy endpoint, and not a stop. No T field is added.

The generic host commitment backend is another explicit frontier. Its `hash`
parameter has type H under a Digest32 dictionary; it is not automatically the
plain leaf hash callback. `PV_W_R_HostBuild` preserves H. The main recursive
translation retains this backend call as an opaque helper until Digest32 and
Commitments and their captured backend fields receive a lifted interpretation.
No fixed-snapshot backend is declared natively adequate.
