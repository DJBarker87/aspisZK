# Runjoin54 — top-down publication composition

Entry: 1adf3ca50f50b8983de4eeb9609731a1301ca463, branch codex/pv-runjoin-20261026.
Budget: 100 Lean attempts, IDs 66900–66999; 66997–66999 audit-only; zero Kani.
Step (4) has not started. Protected prefixes remain read-only.

The target is the exact `PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT` read
with git show from candidate revision 2a484b7a681b16f1904cd781a7ac38d4ecef3219.
Its eleven-module interface closure is reused read-only with source/object
hashes and every imported object fingerprint checked before use.

## Composition design

The first local theorem extracts the actual prepare, salt, finish and publish
successes from `prover.prove_from_semantics`, without replacing any source
call. The conditional typed skeleton will expose seven named links, retaining
r24/sampler, common sample, backend producer, FinishContext, query append,
node append/indices, and publication ordering separately.

Whole ledger rows removed: none. Endpoint and TrustItems unchanged.

## Recorded workflow error

66939 accidentally resubmitted the unchanged failed source from 66938: an
exact-text replacement missed its indentation. Both failed, neither earns
credit. The subsequent source is changed, and the own-input pre-submission
wrapper now rejects any source hash previously rejected for that module.
