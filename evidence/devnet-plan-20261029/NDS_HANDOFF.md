# NDS handoff

**BLOCKED / return to owner:** existing Pool state cannot be wired to a new
verifier through normal registry instructions. Its live registry is frozen,
generation 3, zero authority; ScheduleProfile returns RegistryFrozen before
entry creation. Pool requires this immutable, Pool-bound registry. No verifier
ID is compiled into the Pool; the immutable entry authenticates it.

Stage 1 is committed separately. Stage 2 did not run because of the explicit
STOP instruction. Stage 3 is a blocked runbook/specification, not a deployment
plan ready for approval. No public writes, signatures, local spends or builds
occurred. No crates/programs changed, no keys generated/modified/copied/deleted,
and no push occurred.

Additional findings: payer 3.708326 SOL, below 7.944576440 SOL buffer rent;
permanent deployment plus estimated fees ~7.9542 SOL, conservative transient
reserve ~15.8988 SOL plus future wiring/spend costs. Documented retained host
key paths are absent; actual retention location and permissions unverified.

Recommendation: owner/lead explicitly select a fresh mint/Pool-state demo
under the unchanged deployed Pool/registry programs if that meets release
scope. The normal initialize → schedule → activate → freeze flow can create
that distinct registry without changing the frozen verifier's compiled IDs.
Do not represent this as upgrading the existing Pool or migrating its notes.
If existing-state continuity is required, return a source/architecture proposal
and its invalidated security/artifact gates to the owner.

Exact established claim: inspected source and finalized read receipts establish
the existing-state wiring obstruction, payer balance/rents and missing documented
key paths. NDS_PROCEDURE.md gives references, NDS_RPC.json original responses,
NDS_SOURCE_PINS.json source hashes. Trust retained: RPC/finality, source-to-binary
association from historical deployment evidence, local decoding and SHA256;
no security premise discharged, added or reclassified. NCY release ELF
reproduction and NDQ historical loaded-ELF association are reused. No fresh
release ELF hash or successful local execution was measured. Target not yet
established; L188 current-verifier deployment association remains open.

Next deliverable after scope decision: retained-key location, exact local-only
rehearsal with cloned dependencies, successful release TX1+TX2 receipts, then a
fully specified devnet command sequence for lead review before any public write.
