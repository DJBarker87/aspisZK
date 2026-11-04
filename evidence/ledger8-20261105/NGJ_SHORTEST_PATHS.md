# Shortest entry-to-accept dependency paths

The NGB inventory is a call graph, not an execution CFG: these are shortest dependency paths to the TX1 checkpoint-producing candidate and TX2 acceptance-relation checker. They identify necessary OPEN driver rows; they do not assert that a single graph path contains every call of an accepting execution. All reached sibling callees and domains must also compose.

## TX1

| Position | Row | Status | Function |
|---|---|---|---|
| 1 | TX1:330 | OPEN | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction |
| 2 | TX1:333 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter.rs::process |
| 3 | TX1:344 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 |
| 4 | TX1:345 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned |
| 5 | TX1:328 | OPEN | programs/r1-cost-probe/src/lib.rs::first_decoded |
| 6 | TX1:094 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx1 |

OPEN rows on this shortest path, in order: TX1:330, TX1:333, TX1:344, TX1:345, TX1:328, TX1:094.

## TX2

| Position | Row | Status | Function |
|---|---|---|---|
| 1 | TX2:213 | OPEN | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction |
| 2 | TX2:221 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter.rs::process |
| 3 | TX2:240 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 |
| 4 | TX2:241 | OPEN | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned |
| 5 | TX2:064 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated |
| 6 | TX2:065 | OPEN | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common |
| 7 | TX2:115 | OPEN | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation |

OPEN rows on this shortest path, in order: TX2:213, TX2:221, TX2:240, TX2:241, TX2:064, TX2:065, TX2:115.
