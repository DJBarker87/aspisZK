# Copy fidelity review (lead rulings r, k', r')

Read common instructions again at 04:18 UTC on 2026-10-28: rulings r, k', r'
were newly present. The earlier native codec result kani-6 is SUSPENDED:
QM31::write_le_bytes reaches CM31::write_le_bytes, which calls copy_from_slice
(field.rs:425-426). Its PASS is retained only as a tool observation, never
used as native-link evidence or row closure. The validated KMX patch was not
applied, and no negative control was run. No native codec claim rests on it.
The scalar parser Lean theorem is independent of this Kani invocation.

kani-4/5 timed out and furnish no positive correspondence evidence. Their
possible copy dependence cannot create credit. Earlier kani-1/2 failed before
verification. The remaining charged run uses only scalar u16/usize values and
bit operations, without any array, slice, clone, allocation or copy operation.
Its scope is one packed-lane insertion identity, not the complete schedule.

The generic scope string in kani-6's raw receipt says reachable control cut;
for that invocation the cut was unused: it called the actual aspis-core codec.
This addendum clarifies the label without modifying the raw receipt.
