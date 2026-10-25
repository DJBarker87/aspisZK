# L186 resumed source-to-ELF audit

Source revision: 9e23364d3563ef9d40ccd0865170d82346e2ec28.
Branch: codex/cx-lowering2-20261026. No shipped source edits permitted.
Read AGENTS.md security/proof discipline and section 6, common/local rules,
S2 ownership/plan/diagnosis/interface, C3-BIN route B and S10 ruling,
and predecessor evidence/lowering-20261026/HANDOFF.md.

L186 is P7 toolchain trust plus reproducible three-ELF rebuild plus S10's
140 ordering certificates. No new Lean obligation or trust item is introduced.
Audit every requested packet source pin; collect all mismatches. An old pin
passes only through a recorded exact function-body replacement and a pinned,
standard-axioms-audited equivalence theorem. Historical evidence stays historical.

Host: dombarker@100.108.41.90. Separate private workspace
/home/dombarker/project-offloads/codex-cx-lowering2-20261026.
All builds use MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64,
optimized SBF, -j4. Expected time: compilation and compiler diagnostics.
Host initially has one NP6 scope, 8G maximum; 62GiB physical RAM, 55GiB safe
reservation ceiling. No other worker's files or scopes will be modified.
Budget initially SBF 0/6, Kani 0/0, Lean 0/10. No theorem added; axioms N/A.
No premise removed yet. Target not yet established.
