# NKS Pool production inventory

Target not yet established. Inventory and assessment only: no proof, ledger edit, trust change or promotion.

Frozen source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; Pool ELF inherited pin `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` (not rebuilt). Branch `codex/cx-pool-inventory-20261107`. Writes restricted to this evidence directory; no shipped source changes.

Budget ceiling: 0 Kani, 15 Lean (existing statements only), 6 MIR/Charon scopes, 0 extraction. No scopes launched yet. Host workspace, if needed: `/home/dombarker/project-offloads/codex-cx-pool-inventory-20261109`; own target directory, no cache writes. All host builds require admission allowed=true AND exit 0, at least 40 GB free, one scope, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.

Stages: (1) authority and source roots; (2) compiler-backed closure and overlap; (3) obligations, tractability and estimate; commit after each stage, never push.

Status: reading authority and predecessor evidence; exact finite Pool closure not yet established. NKN basis has 599 verifier rows and zero production Pool consumer occurrences. RuntimeCpiReadonlyEntry7 remains pending and unused; entry admission supplies initial fields only. K086 production reachability/exclusion remains unproved.

Stage 1: retained exact deployed Pool SBF diagnostics read-only from Low2; all 133 repository compiler inputs agree with the frozen revision. Fourteen dispatch alternatives listed, nine conservative ON roots and five OFF routes. No host write/build scope or prover run.
