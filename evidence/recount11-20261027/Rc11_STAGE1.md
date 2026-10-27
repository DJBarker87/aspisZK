# Stage 1: read-only kernel audit

No new theorem or proof. Rc11_Candidate imports ARX_Root unchanged and prints
both complete root types plus ARX's named declaration and both axioms lists.
Rc11_Inventory reopens all 44 Rc10 family inventories and the changed account
and admitted-image definitions, including 24 standard-only axioms reports.

Fresh Rc10 kernel type is whitespace-identical to the retained Rc10 AFTER type.
Rc11_001: exit 0, wall 2.527470666973386 s, peak RSS 5549064 KiB, swaps 0.
Rc11_002: exit 0, wall 3.2953551490209065 s, peak RSS 5558572 KiB, swaps 0.
Both used one scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64 and Lean -j1 -M7000. No retries, timeout or memory kill.
The exact source revision/hashes, dependency fingerprint, commands, cgroup
checks and full axioms lines are in Rc11_00*/receipt.json and stdout.log.
Lean budget 2/20; Kani 0/0. No package replay or shipped-file changes.

The provisioned branch is codex/cx-recount11-20261027 (the prompt's earlier
branch suffix was 20261026); no branch switch or sibling-worktree access.
