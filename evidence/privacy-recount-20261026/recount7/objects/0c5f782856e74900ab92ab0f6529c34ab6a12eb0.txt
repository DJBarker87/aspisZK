# Copy fidelity review (lead rulings r, k', r')

Read common instructions again at 04:18 UTC on 2026-10-28: rulings r, k', r'
were newly present. The earlier native codec result kani-6 is SUSPENDED:
QM31::write_le_bytes reaches CM31::write_le_bytes, which calls copy_from_slice
(field.rs:425-426). Its PASS is retained only as a tool observation, never
used as native-link evidence or row closure. The validated KMX patch was not
applied, and no negative control was run. No native codec claim rests on it.
The scalar parser Lean theorem is independent of this Kani invocation.

kani-3/4/5 timed out and furnish no positive correspondence evidence. Their
possible copy dependence cannot create credit. Earlier kani-1/2 failed before
verification. Receipt tally confirms six runs already used, so no further Kani run will launch.
The drafted packed_lane_insert harness was never run and has no proof credit.
The earlier checkpoint incorrectly called kani-3 a reservation refusal; its
raw receipt records a charged 180-second timeout. The receipt tally prevails.

The generic scope string in kani-6's raw receipt says reachable control cut;
for that invocation the cut was unused: it called the actual aspis-core codec.
This addendum clarifies the label without modifying the raw receipt.

Receipt comparison also reveals kani-4 repeated kani-3 with identical source
hashes, flags, bounds and timeout. That retry was contrary to the no-unchanged-
rerun rule; it consumed one of the six runs and adds no evidence. Both failures
remain archived. No further run will be justified from that duplicate.
