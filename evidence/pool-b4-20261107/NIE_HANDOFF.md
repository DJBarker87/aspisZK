# NIE incremental handoff

Branch codex/cx-pool-b4-20261107. Scope: Pool production prefix B, part 4. No push, shipped-source edits, wallet/key operations, or claim of release closure. Target not yet established.

Stage 0: read the S2/NHP handoffs and binding rules. NHP K086 is retained by hash. NIE_ACCESSORS.json inventories seven frozen Pool accessor sites (including the vault authority site omitted from the brief's illustrative list), with conservative direct callers. This static inventory is not a native borrowability proof. Each site's caller/alias/callee/CPI borrow-release obligation remains OPEN. No counterexample input or transaction shape is constructed.

First deliverable: NIE_BORROWABILITY.md, native caller-prefix cuts with controls and exact model association where possible. No abort-prefix assumption replaces caller borrowability. Borrowability failures are liveness obligations, not soundness claims.

Budget ceiling: 120 Kani, 80 Lean, 2 NHR_stage.py extractions. Used 0/0/0. Host scopes require admission exit 0 and allowed:true, 6G/8G/swap0/tasks64, Lean -M7000. Sequential scopes initially. Optimized/offline native graph checks before every run and unchanged lock afterward. Retain the owned prefix cache, reuse NHP/NHC/NGK exports read-only, never delete keys or foreign files.

Read-only host inspection reports 97% disk use and 57 GiB available. No host mutation or launch yet. No new theorem exists, so axioms/resource fields are not applicable to stage-0 inspection. Exact source revision and per-file hashes are in NIE_ACCESSORS.json; stage commits pin the inspection scripts.
