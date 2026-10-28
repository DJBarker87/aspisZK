# NCF entry contracts

op29/30 contracts hold on all valid typed V2/V1 entries and every u64 slot.
Requires true; exact native status/activation/retirement Bool; default readonly
contract frame. NCF_K002/K006 pass actual getter proof_for_contract. The wrapper
controls NCF_K003/K007 invoke the same actual getter and invert that predicate;
both fail exactly their postcondition. No field or copy replacement is involved.

NCF_K004/K008 use stub_verified and assert the exact predicate. Both pass;
NCF_K005/K009 assert its negation and fail exactly the comparison assertion.
These harness callers are local contract consumers, NOT authentication callers.
Runtime-formatted assertion-message warnings are retained, as in NCC's pilot.
They do not affect the successful baseline or add another failed check.

NCF_EntryContract.op29_exact/op30_exact prove that NBX's existing typed cohort
candidates return ok of exactly the same status/interval predicate. NCF_L003
passes; axioms propext/Classical.choice/Quot.sound only. The local classical
decidable equality supplies enum equality, not any native assumption.
No installed AeneasExtraction component or SDK call-site association is inferred.

Every run freshly validated the complete frozen dependency graph offline and
kept Cargo.lock unchanged. Native tool/config/source hashes and caps are in
per-attempt receipts; audit NCF_STAGE1_AUDIT.json checks matched source/control
pairs. Own module path typo caused NCF_K001's compile failure; no proof credit.
NCF_L001 transport is unresolved and never resubmitted; NCF_L002 failed to
elaborate a missing Decidable instance and receives no credit. L003 changes the
source to fix that error. No timeout/memory kill/cap increase or unchanged
regression rerun occurred. Cache and resolved Aeneas pins: L003-object-pins.json.

Later policy pilots are separate and EXCLUDED from bridge credit: K059/K066
fail an extra ghost precondition. They do not affect the valid op29/op30 pairs
above. See NCF_SDK_PILOT_SCOPE.md and the final handoff audit.
