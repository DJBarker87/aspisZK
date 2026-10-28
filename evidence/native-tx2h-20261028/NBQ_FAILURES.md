# Retained failed attempts

- NBQ_K002: harness array equality reached builtin memcmp with unwind8, 1 failed/15 undetermined. No source-behaviour finding. Replaced array assertions with four scalar comparisons in NBQ_u06c.patch; K003 passes. No timeout or memory limit raised.
- NBQ_L004: malformed tuple construction for nested canonE in finish proof. Other roots printed standard axioms; finish's diagnostic sorryAx is excluded. Replace with explicit nested conjunction proof before credit.
- NBQ_L006: redundant rfl after simp had already closed checked_invalid; removed the extra tactic. L007 passes all roots.
- NBQ_L008: rewriting the state before unfolding Bound left unreduced old projections. Replaced with substitution of the full state. L009 passes update/initial/step, standard axioms only. Diagnostic sorryAx lines excluded.
