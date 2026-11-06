# Retained failures and replacements

No assigned member has a remaining local proof step after the final gate. Target not yet established.

K003 default solver and K004 CaDiCaL each timed out on the scalar raw-integer product segment. The same original target with changed backend Kissat passed K005; its inverse failed K006. No cap/time limit increased; no timed-out shape rerun unchanged. Minisat was unnecessary after Kissat passed.

Own input failures: K001 allocator_api compile error; K002 owned gate quoting; K052 missing QM31 Arbitrary. Replacements are cfg(kani)-only support, not frozen body changes. The final QM31 and Range fidelity families are re-established coherently in K056..064 and K065..069; earlier families remain historical/excluded. E001 was a missing-source prelaunch exclusion (no Charon/Aeneas); E002 succeeds. S002's binary collector failure was recovered read-only after exit0. Lean draft diagnostics L004/006/007/011/016/030/031 are retained, excluded; changed repairs compile. NKJ_RUNNER_REPAIRS.md records owned script repairs.

Predecessor whole-function/cell/outer-step timeouts and actual extraction2731 remain retired; none was replayed unchanged. The new native route is source-ordered scalar/cache/write/index cuts, never a whole cell/product-buffer differential.
