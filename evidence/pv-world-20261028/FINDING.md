# W-CARRIER-1: world indexing must retain destructor-accessible state

This logical counterexample passed focused attempt 36002 (exit 0; five empty
axiom reports). It is narrower than an impossibility of sidecar semantics.

The proposed generic interpretation of effectful Drop over **only** the current
OS Observation World needs an adequacy projection from native worlds to that
World. The current fields are entropy/file/time/worker tapes and cursors. Keep
all those fields fixed and vary the external AtomicBool read by FXM's zero-sized
destructor. The input value is identical. Native normal return and panic differ
in the existing checked witness; projection to the unchanged tape/cursor world
forgets the flag. A state/error/trace interpreter indexed by that projected
World therefore receives identical inputs and cannot reproduce both results.

PV_W_CarrierObstruction.no_factor proves this for any World and any pair of
distinct outcomes. no_state_interpreter specializes to the full threaded
interpreter, including post-state and trace; inspecting its outcome already
contradicts adequacy. no_forgotten_flag_interpreter instantiates the two-world
normal/panic witness. retainedFlag_result shows nonvacuity after retaining the
flag as ordinary interpreter state. No T field is involved.

Native evidence is REUSED, not rerun: branch codex/pv-fxmem-20261028,
evidence/pv-fxmem-20261028/drop-counterexample-02/output.log (32 paired cases,
real core::mem::drop, optimized compiler, same zero-sized input, distinct
normal/panic outcomes, one destructor entry). FINDING.md on that branch states
its scope and compiler pins. This job does not claim that custom destructor is
reached by the deployed prover, or promote finite validation to a Rust memory
model or binary-erasure theorem. The new logical result identifies a necessary
adequacy condition on any proposed World projection.

The finding does NOT refute an encoding of the flag into a redesigned carrier,
an enriched interpreter state with a proved Observation projection, or a
restriction proved for the actual reached destructor types. It does refute the
uniform claim with a projection that forgets the flag. Encoding such memory in
an unrelated entropy/time/file tape changes that tape's specified meaning and
requires a new carrier-binding proof. Merely making the same fixed dictionary
a function of this insufficient projected world does not supply that proof.

Consequences: retain generic V170 effectful cases and the allocator/memory
interpretation obligation. The requested complete all-effect caller theorem
cannot be claimed from the current carrier and pure lifts. File-only and
entropy-only sidecars remain viable independent work; this is not a
counterexample to them. Under the user's checked-counterexample stop condition,
report the precise projection failure, the proved calculus and OS obligations;
do not fabricate a row-closing instance by changing the observed carrier.
