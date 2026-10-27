# L186 lowering audit: stage 0

Branch: codex/cx-lowering-20261026. Source revision: 14668ba43975d2078f431c126bb728952e29b56a.

Read root AGENTS.md security/proof discipline, common/local rules, and the
S2 ownership handoff, plan, diagnosis, interface, route B ruling (01:20)
and S10 ruling (2026-10-25 13:35). Historical requested paths resolve under
docs/research/100bit-spend-path-20261013/.

L186 is P7 plus reproducible pinned ELF rebuild plus 140 ordering facts.
Audit source pins first; stop on a source mismatch per owner instruction.
No source equivalence or historical receipt will silently replace exact identity.

Budget: SBF 0/6, Kani 0/0, Lean 0/10. No build or proof launched.
No shipped files changed. No theorem added; axioms audit not applicable.
Caps for any future host build: MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Optimized Rust, -j4.

The next deliverable is a source-pin checker with exact evidence locations.
No premise discharged, added or changed. Target not yet established.
