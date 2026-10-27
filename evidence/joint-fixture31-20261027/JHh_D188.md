# Narrowed D188 boundary

These are Lean model fixture claims, not new translation/native/ELF claims.
No new D188 credit is assigned. The owner-cleared bodies verify_in_place,
update_residue_row, add_small_base_p, and BatchedWeights::finish are retained
as cleared; low_base_p_digits is excluded; its native bridge belongs to LPk_, as the
owner specified. This JHh continuation neither replaces nor rechecks that bridge.

Reached or transitively used bodies whose mutable element/iterator writes
need their existing native/P6 association checked include early_powers
(weights.rs:21), the Weights new/pair construction and field tables
(weights.rs:154–218 and later helper arrays), canonical::Dot::push
(fast_pairing.rs:119), the four-dots scalar accumulator writes (fast_dots.rs:27–43), QueryGeometry prefix/backward inverse writes
(verifier.rs:172), BatchedWeights::new raw element writes (verifier.rs:211),
BatchedWeights::push's &mut self.raw[index] call (verifier.rs:217–219), and
accumulate_batched_with_node's basis element writes (verifier.rs:279–280).
Direct indexed assignments are conservatively listed because the extracted
accessor restoration is what must be checked. No new native differential was
run. This is an inventory of association obligations, not a finding that all
these bodies lose restoration. The actual reached release branch does not
write a.weights[j] in the cfg(prover) branch.

The JHh writer-image and chronological trace theorems do not establish native mutable-borrow restoration. The append-content writer is a Lean content interpretation; its native/runtime/source-to-ELF qualification remains. No additional D188 credit is claimed.

This job adds no native or D188 clearance. New checksum proofs are mathematical SHA equations on retained bytes.
