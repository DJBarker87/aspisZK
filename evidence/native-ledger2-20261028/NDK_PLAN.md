# Ledger refresh scope

Pinned research head `898a8b0da7703af67b676b18b575236940830283`; previous NCZ snapshot `1d7752908191642fc8383c99bbadfb46fab8850c`.

Stage 1: inventory merged evidence and retention/feature rules. Stage 2: independently reconstruct the current ledger, add reviewed local associations, recompute coverage/frontier. Stage 3: run inherited and extended mutation checks and ordinary validation; record exact handoff and receipts. Commit each stage, never push. No Lean or Kani launches.

Audit complete theorem statements and their retained domains (AGENTS sections 3/8). Only pinned merged evidence can supply local conditional credit; composed execution remains open without per-edge certificates. Rules 12–15 apply. No NDE/NDH/NDI file exists in the pinned merged tree; unmerged branches are outside scope.
