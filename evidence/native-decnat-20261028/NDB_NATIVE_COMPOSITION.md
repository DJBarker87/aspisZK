# Native composition obligations

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, deployed features.
The native checks below are ordinary harnesses, not proof_for_contract or
stub_verified substitutions. KMX is the sole substitution; the paired copy
fidelity check is K003/K004. No function-pointer-dependent credits are used.

Source structure:
* op48 decode_master_box: decode_pool_v1_pair_forest_master_v1; map all inner
  errors to InvalidAccountData; allocate Box on success.
* op49 decode_checkpoint_box: decode_pool_v1_pair_forest_checkpoint_v1; same map.
* op50 decode_lane_from_pool_release: its own header/length/binding/zero/master
  checks; canonical root; twenty native frontier iteration steps, each with
  canonical decode and occupancy guard; final empty-root guard; Box construction.

Native loop step harnesses select nth(k) from an actual iter_mut().enumerate()
starting on arbitrary typed pre-state. They assert the enumerated index is k,
the new selected row equals the read window, and an arbitrary other coordinate
is unchanged; checkpoint also asserts the capacity rejection predicate. Thus
they address iterator association omitted by NCV's indexing-only fragments.
The frontier step takes an arbitrary predecoded row, so the canonical child and
its input-window association must be composed separately. It is not a native
proof of the complete lane decoder.

NDB_WindowGeometry gives exact original/sliced window identity and bounds at
320+8*k (master),112+8*k (checkpoint),80+48+32*level (lane). NCV_CallerDomains
gives identity/policy/digest child lengths. No precondition about canonical
field limbs is needed for Box value/error-map checks: arbitrary u32 carriers
are included. Native arithmetic multiplication is never used.

The Box and map-error harnesses are isolated copies of the wrapper continuation,
with arbitrary full typed records and errors. They are NOT actual enclosing-call
contracts and do not by themselves prove original allocation/context association.
Any final bridge must preserve Result< Box<record>, ProgramError > and the original
input/account frame. No opaque whole-body equality premise is disguised here.

Composition under the owner-approved option A is a tool-trust reclassification,
never a logical premise-removal claim. Until every callee domain and original
control-flow/allocator association is discharged, all three top bridges stay OPEN.
