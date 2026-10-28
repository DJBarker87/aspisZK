# NBA stage 6: symbolic eager materialization

L038 checks all generic eight-slot stores/readbacks. L044/L047 check the
materialization continuation distribution with standard axioms and no option
changes. This is a fresh NBA factor of the PublicPreparation query definitions;
it has no native/kit association credit by itself.

L048 exceeded Lean's fixed kernel -M7000 allocation. Full resource review and
replacement are in NBA_L048-REVIEW.md. The kernel rejected the declaration;
its nonstandard diagnostic axiom line is excluded, not an accepted theorem.
The failed broad proof was replaced with explicitly ordered, one-operation
rewrites using the named eight-slot symbolic lemmas. L049 reaches the result
in4.933 s but exits1 because a redundant final rfl sees no goals; L050 removes
that redundant tactic. No caps, timeouts, heartbeat or recursion options raised.

The full public query/body factoring join remains separate. L040 and L046
hit the unchanged recursion limit; L041/L042 local pair-binding reduction and
L043 a reserved-name parse failure are retained. No raw emission, inherited
cohort definition or other worker's source was edited.
