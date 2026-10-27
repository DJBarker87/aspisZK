# Allocation 8 receipts

Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Each exact source snapshot, input/object hash, raw output, full printed axioms and timing is retained beside resume8-attempts.jsonl. No axiom report from a rejected attempt is accepted.

| ID | Exact target | Exit | Validation | Wall | Peak RSS KiB | Swap | Source revision | Axiom reports |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 41505 | R1Z/PV_Src_ExternalBlockStep | 1 | REJECTED | 0:02.11 | 4126720 | 0 | 6ddc8e0ea0 | 3/3 |
| 41507 | R1Z/PV_Src_ExternalBlockStep | 1 | REJECTED | 0:01.96 | 4129772 | 0 | 6ddc8e0ea0 | 3/3 |
| 41508 | R1Z/PV_Src_ExternalBlockStep | 0 | standard | 0:01.98 | 4149728 | 0 | 6ddc8e0ea0 | 3/3 |
| 41509 | R1Z/PV_Src_ExternalBlockWrite | 0 | standard | 0:01.87 | 4142996 | 0 | 6ddc8e0ea0 | 2/2 |
| 41510 | R1Z/PV_Src_ExternalCopyBlockStep | 0 | standard | 0:02.05 | 4142616 | 0 | 6ddc8e0ea0 | 2/2 |
| 41511 | R1Z/PV_Src_ExternalBlocksCopy | 1 | REJECTED | 0:01.90 | 4122292 | 0 | 6ddc8e0ea0 | 1/1 |
| 41512 | R1Z/PV_Src_ExternalBlocksCopy | 0 | standard | 0:01.90 | 4143432 | 0 | 6ddc8e0ea0 | 1/1 |
| 41513 | R1Z/PV_Src_ExternalWritePrefix | 1 | REJECTED | 0:01.99 | 4121264 | 0 | 6ddc8e0ea0 | 1/1 |
| 41514 | R1Z/PV_Src_ExternalWritePrefix | 0 | standard | 0:02.07 | 4145244 | 0 | 6ddc8e0ea0 | 1/1 |
| 41515 | R1Z/PV_Src_ExternalCopyPrefix | 0 | standard | 0:01.91 | 4141812 | 0 | 6ddc8e0ea0 | 1/1 |

Charged Lean attempts: 10/60. Reservation refusals: 7, uncharged. Next unused ID: 41517.

## Shared replacements

Each overwritten shared source/object has its preimage under the assigned host job snapshots/resume8-ID. Accepted own object copies are rebuildable caches; no binary is committed. All changed dependent outputs, or exact pending exception reasons, are recorded in the gate JSON.

## Kani runs

Optimized compilation then named CBMC step; 6G/8G/swap0/Tasks64, one scope at a time. Kani has no #print axioms (N/A); exact input hashes and metadata retained.

| Target | Exit | Wall seconds | Peak RSS KiB | Cgroup peak bytes | Swap | Revision |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ['timeout', '900', 'taskset', '--cpu-list', '0-3', 'cargo', 'kani', '--no-assertion-reach-checks', '-Z', 'stubbing', '-Z', 'function-contracts', '-Z', 'unstable-options', '-p', 'aspis-statement', '--lib', '-j', '4', '--exact', '--harness', 'pool_v1::pair_forest_copy_builder::records_proofs::empty_roots::pv_srcid7_helper_prefix11', '--output-format', 'terse', '--cbmc-args', '--unwinding-assertions', '--slice-formula'] | 124 | 900.003123 | 15296 | 5141737472 | 0 | cbcac1bd088222f39f08e09506b1e0d5cc003bbe |
