# Production prefix B — working inventory

B remains OPEN. Frozen implementation: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Actual entry is processor -> pair_forest::process_pair_forest_terminal_v1 ->
process_pair_forest_terminal_with_verifier_v1; compact dispatch lives in
pair_forest_dispatch.rs. Account decoding and marker creation are in pair_forest.rs
and their actual callees. The order is Pool admission -> marker creation ->
selected verifier CPI -> verifier pool_route::admitted -> return-data read.

Local metadata helpers may inspect only key/owner/flag fields. Their initial
Kani records retain arbitrary key, owner, flags, lamports and epoch; one-byte
data allocations are fixture carriers. These tests alone do NOT establish a
production arbitrary-buffer physical interpretation or root PacketDomain.
No local pass is promoted to a composed NDT row.

The hint splitter uses one arbitrary returned body byte and four hint bytes;
it executes no whole-buffer copy or native byte loop. K002 fixes K001's
length-four skipped assertion; K003 is the matched failing corruption.

Native contracts need exact modifies clauses and per-shape fidelity controls
before stub_verified is used. No stub_verified is used here. No field product,
SHA implementation, function-pointer comparison or writable static is used.
