# First-half library model fidelity audit

Stage 1: scope pinned; verdicts pending. No premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 retained.

Assignment: first 92 of 184 rows whose inventory counterpart is exactly
`library model`, sorted by declaration name (stable ties). Last assigned:
`core.iter.traits.iterator.Iterator.all.default`; the second half begins
`core.iter.traits.iterator.Iterator.any.default`. Full hashes and row identities:
`KSC1_assignment.json`. Several inventory-labelled rows are Aspis carriers,
helpers or shipped-function stand-ins; a library label cannot supply fidelity.

The KSA dependency witnesses and raw-body occurrence counts are retained as
static prioritisation data, not dynamic call frequencies or reached-path proofs.
Neither inventory proves actual execution frequency on the adopted path.

Limits: 80 Lean attempts, 10 Rust runs, zero Kani; one admitted scope at a time.
All existing source, candidate and host objects remain read-only. Only KSC1_
modules and this evidence directory are changed. No shipped-file change; no
ELF rebuild triggered. No key action.
