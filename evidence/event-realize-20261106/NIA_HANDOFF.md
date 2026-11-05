# NIA native event realization handoff

Branch: codex/cx-event-realize-20261106. Work in progress; target not yet established.

Scope: NFS event interpretation, complete prepared-constructor traces, failed/diverging scalar packets, then conditional TX1 cut composition. Only NIA modules and this evidence directory may change. No shipped source edits, pushes, wallet operations or sibling worktree edits.

Budget: 40 Kani, 80 Lean, 1 extraction (NHR_stage.py only). Serial admitted scopes, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; Lean -M7000. Host disk observed 97% used (57G free); retain a small own cache and reuse coherent pinned objects.

Initial inspection: NHZ events_from_cuts is conditional on physical packet existence and exact native ordering. NFS cuts record NFP callee events; arbitrary base callback slots survive NFS_QueryOps.installed. Result equality alone does not prove empty digest effects. NHS_PreparedPacket.source currently proves only successful Result, and NHS_QueryFailures covers Result Error/fail/div without earlier scalar events. NGT successful Block has three ok edges only. No trace or native credit is claimed yet.

Retained hypotheses: op9 and full native parent ordering, physical observer fields, approved runtime trust rows and original L154 parameters. No row promotion expected.

Validation, exact targets, source/dependency hashes, revision, exit/wall/RSS/swap and printed axioms will be recorded in NIA_ATTEMPTS.jsonl and per-attempt receipts. No ELF rebuild is triggered unless shipped source changes (none planned).
