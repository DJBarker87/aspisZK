# Prover commitment part 28

Base `26b922be6`, branch `codex/cx-prover-commit28-20261022`.
Target not yet established. Work and evidence are recorded incrementally.
The final assigned Env J range is 7800–7999; used receipts are skipped.
No shipped files or concurrent-owned modules are changed.

## Continuation port

The retained control21 suffix contains scanner selection, all 22 trace writes,
query rejection and rho. The port uses an explicit state transformer over
Aeneas Result, with pure Result operations lifted into it. Digest calls consume
the current machine state instead of the stale copied hash token. The full
returned machine is observable at the continuation boundary. A mechanical
source-port check will retain every non-digest operation in order.

Pending: generic interpreter validation, the concrete suffix, semantic/circle
and full walk composition, replay reset, retry/programming/serialization,
shippedProverExperiment, both WholeRunJoins and endpoint specialization.
RustProverRefinement remains explicit until those concrete obligations close.
