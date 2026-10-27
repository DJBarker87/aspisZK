BEh_Scope formalizes two-slot accepted Result/full observable carrier/attempt-log
agreement and rejected acceptance/attempt-log agreement. It intentionally imposes
no rejected-state equality. BothSlots is a specification, not a concrete instance.
BEh_Countermodels proves four interface countermodels: accepted result/log does
not determine state; rejected final-state equality is unnecessary; equal counts
do not identify order; equal rejected observation does not identify history.
These are not shipped-source counterexamples. Attempts001/002 passed first try;
per-attempt receipts contain exact target/command/revision/source/deps, cgroup,
exit/wall/RSS/swap and all seven axioms audits (standard axioms only).
No top theorem changed, zero premise removal; budget2/30 Lean,0 Kani.
