# NBX U04 — ruling (s) native instances

Status: OPEN. The historical NBU “not a soundness obligation” classification
is superseded by ruling (s). Retain all inherited NBU/NBN results without
re-proving them. Each op15, op23, op25–34, op48/op49 requires representability,
frame and SAME-argument call-site association for one real native instantiation.
No body-fidelity or adapter-law premise is introduced.

Slot inventory correction: op31 = V1 registry, op32 = V1 entry,
op33 = V2 registry, op34 = V2 entry, per coherent AdapterRw.Ops.
Digest/error remain op43/op44.

Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
The source and inherited ELF pins are unchanged. This is no release claim.

## Stage 2: candidate value selection and local native frames

NBX_SlotValues uses the original AdapterRw carrier and updates only the
existing op15/op25–30 fields. op15 reuses PoolS2_PolicySource unchanged.
The six getter functions have full typed domains (no validity/canonicality
precondition), exactly one explicit record, plus current_slot for op29/op30.
The candidates add no adapter-law hypothesis. The selection/continuation
lemmas are local SDK composition, not the whole headline extraction theorem.

NBX_SOURCE_ASSOCIATION.json records every native occurrence in frozen
r1_pool_adapter.rs and its owned boundary alongside the corresponding emitted
SDK call. op15 receives master.verifier_policy; op25–28 receive the same decoded
registry; op29/op30 receive the same decoded entry and current_slot. This file
is a source inspection artifact, not a proof of the enclosing caller.

K003–014: actual getters on arbitrary complete records and arbitrary slot,
with arbitrary-coordinate input and ambient frames. Each positive has its
matching failing inverted assertion under identical KMX/frozen configuration.
K015–022 additionally check both retirement getters, status decoding and
required_binding_is_zero. These are local native evidence, not whole U04 closure.

Additional attribution correction: op15 itself is only
validate_verifier_policy_v1(&master.verifier_policy). Identity and policy byte
decoders are reached below op48/decode_master_box, not standalone op15 calls.
op48/op49 include the actual Box allocation and ProgramError mapping; a pure
inner struct decoder does not by itself close that wrapper's instance.

Validation stage2: NBX_L002 compiled NBX_SlotValues with exit0,
5.180256306s, peakRSS5,375,668KiB, swaps0. All nine printed roots use no axioms
or only propext/Classical.choice/Quot.sound. L001 is rejected, not evidence.
K003–022 establish ten positive/failing-control pairs; K001/K002 were own
compilation-input failures and are excluded. Exact sources, commands, frozen
graph, lock pre/post hashes, dependency/tool pins and cgroups are in per-attempt
receipts and NBX_ATTEMPTS.jsonl. No native whole extraction is claimed.
