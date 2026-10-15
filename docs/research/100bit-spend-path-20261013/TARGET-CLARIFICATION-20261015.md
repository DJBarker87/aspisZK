# Security target clarified on 15 October

The user explicitly selected: **“I mean 100-bit per-attempt soundness, without
grinding credit.”** This replaces the stronger working scenario of an absolute
failure probability of at most `2^-100` after `2^64` adversarial hash queries.
The protocol must remain transparent and trusted-setup-free. The transaction
limit remains two for verification and settlement, excluding proof staging.

The parameter target is therefore the error of one transcript attempt under
the protocol's challenge experiment. No proof-of-work bits are added, and no
error probability is divided by adversarial work. Repeated/adaptive oracle
attempts still need the stated query-dependent Fiat–Shamir bound; the
clarification does not remove its `Q` factor or prove its premises.

The current exact arithmetic ledger is sufficient for this numerical target.
Its largest row is approximately `2^-105.136475`. Even the loose arithmetic
bound `33 * max_row` is approximately `2^-100.092081`. Replacing the 25
semantic rows by their existing checked sum `303100 * (1/P^4 + 1/2^256)`
and adding the six remaining ledger rows gives approximately
`2^-104.426726`. The [exact-rational calculation](per_attempt_budget.py) records
its inputs and results in [per-attempt-budget.json](per-attempt-budget.json).
These are conditional arithmetic calculations, not a theorem
that the concrete verifier implements all of those experiments. Collision,
commitment, source and privacy obligations are not silently included in them.

Consequently, widening the semantic challenges or increasing the query count
is deferred. The current `Q <= 35` result concerns the stronger **absolute
whole-experiment** bound; it is not a parameter blocker for the clarified
per-attempt target. The next security work is the concrete classifier and
extractor, the round-density and acceptance implications, the authenticated
source correspondence, and the privacy simulator and mask-image obligations.
The guarded shared-point arithmetic optimization remains useful for compute
headroom and does not change the challenge distribution.

The [current ledger](security-ledger.json), [semantic prefix proof boundary](SEMANTIC-PREFIX-BRIDGE.md),
[Fiat–Shamir interface](FS-REUSE-REMAINING-20261015.md), and
[privacy boundary](PRIVACY-RANK-PATH.md) retain their separate scopes.
