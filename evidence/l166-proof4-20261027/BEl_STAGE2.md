Historical stage checkpoint; final outcomes are in BEl_KANI_RUNS.md and BEl_HANDOFF.md.

# Recorder/leaf gates

The full Rust recorder copied each part and concatenated address. K01 was an
internal Kani compiler error on Infallible equality. K02 and K08 were incomplete
at the120second harness limit. The Kani driver returned0 and a misleading
manual success summary without VERIFICATION SUCCESSFUL; both are excluded.
K08 changed the copy shape from flat_map to explicit3-part extend_from_slice,
then stalled in builtin memcmp unrolling. No unchanged timeout was rerun.

K03 diagnosed builtin memcmp unwinding at4 plus legacy assertion-reach checks.
K04's semantic assertions all passed, but its cover was reported as FAILURE
by the old-format driver. It is conservatively excluded. K05..07 are unambiguous
VERIFICATION SUCCESSFUL: all832bytes and arbitrary32-byte reply, each tree's
full part lengths, universally selected part/byte/call, and raw digest equality.
No stubs, no function contracts, no hidden successful-log premise.

K09..11 verify the exact local leaf-loop cut against the owned reference for
all three trees. Arbitrary scratch, used<=position<12, either batch start,
all key bytes, opening bytes and reply; both rejection and continuation stay
in the domain. Exact returned status/cursor/selected ordinal/used count,
every scratch coordinate and every call coordinate agree. The caller's
actual selected opening/position/keys must still be supplied at the reached cut.
This does not reprove or replace the existing P6 scratch induction.

K12 verifies every8-byte padding word: shipped little-endian nonzero iff
reference any nonzero byte. Whole padding traversal still needs composition.
K13 probes the whole batch with an arbitrary684-reply chronological tape.
The first observed bottleneck is Kani's nested-array Arbitrary constructor,
not a shipped source loop. A flattened21888-byte tape is prepared as an
identically scoped replacement if K13 times out; no cap increase.

Lean recorder entry/finish and exact suffix reconstruction, and returned-call
operational models for pure/stateful raw backends, compile with only standard
axioms. These models do not on their own establish a physical batch instance.
L166 and the actual-root ledger remain unchanged.
