# Excluded steps

L001/L002: API inspection queried absent names. Discovery errors, no closure credit.
L003: eight-word byte-read proof needed explicit lift normalization and finite-list conversion. L004 passes with the same mathematical statement.
L005: own Lean indentation error. L006 elaborated the proof and isolated the missing finite high-word cases; L007 supplies those cases and passes.
L009: own do-expression parentheses error; L010 then exposed an unnecessary tactic after solved goals; L011 passes after removing it.
L012: typed chunk constructor's attached-list projection needed definitional normalization; L013 passes.
L014: scan proof needed explicit typed get bounds and an error-carrier reduction before loop_done. L015 repaired these; its broad simp on the scalar port hit maximum recursion depth. L016 uses only the exact port equality and the single rejecting branch, with unchanged caps; passes. No depth limit was raised.
L018: parser substitution using broad congr reached deterministic heartbeat exhaustion (17.01652017980814 s, peak 5,919,736 KiB, swap 0). Tool limit in automatic congruence, not mismatch. Excluded; never rerun unchanged. NGV_Monad and L020 replace it with explicit bind-by-bind cuts. No heartbeat limit was raised.
L022: dependent match in validator totality required simp-only normalization before selecting the bounded error branch; L023 passes.

Audit setup's first reservation was allowed:false (projected reservations >55 GiB). No copy or build launched on that refusal. The own setup wrapper was repaired to preserve refusal receipts and implement 3-minute wait/retry, with unchanged reservation validation; retry 1 admitted. This is contention, not an infrastructure bypass.
