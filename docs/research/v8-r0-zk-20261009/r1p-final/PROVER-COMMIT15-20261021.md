# Prover commitment part 15 — fixed observer and source transport

Base: `542fe958f`; branch `codex/cx-prover-commit15-20261021`.
No production source, peer-owned proof file, wallet, key, or frozen artifact is modified.

## Scope and statement audit

The part-14 counterexample concerns unrestricted replacement observer programs.
The new endpoint explicitly specializes to `fun adv => adv.prog` of the
constructed `fsR1P` source. Both sides of the old endpoint are literally that
same model. Identity joins at this endpoint must not be described as shipped
Rust execution refinement. The actual source integration remains a separate
obligation, even if the named model premises can be deleted.

## Stage 1 — fixed observer

Work in progress. Exact statements, deletion evidence and host receipts follow.

The explicit specialization is `R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted`
in `R1Z/ProverCommitFixedEndpoint.lean`. `observer_program` is fixed to the
constructed source adversary's own `R1Adv.prog`. All adversaries and their
decision functions remain quantified. No query budget, failure event,
randomness carrier, conclusion or numerical bound changes.

J8391 compiles `ProverCommitFixedObserver`: exit 0, 1.55 s, peak RSS
3508116 KiB, zero swaps. J8395 compiles the explicit specialization with
both old join binders retained but unused: exit 0, 6.63 s, peak RSS
4176568 KiB, zero swaps. All accepted printed axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Base revision is `542fe958f`;
exact new source snapshots, SHA256, transitive object fingerprints,
commands/errors/timing/axioms are in the part-15 `lean/` receipts.
J8390 is an excluded missing-instance diagnostic; J8392–8393 are excluded
notation precheck errors; J8394 is an excluded tactic-transparency failure.
No failed generated `sorryAx` diagnostic is adopted. J8395 removes the
unnecessary rewrite tactic: structure eta equality supplies identity directly.

The host launcher uses existing slot locks until 17:00 London, per the lead,
and exactly 6G/8G/no-swap/64-task scopes. No host dependency cache is rebuilt.
The new endpoint is a new file; no imported shared source/object is replaced.
