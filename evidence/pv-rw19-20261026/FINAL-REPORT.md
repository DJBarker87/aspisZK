# pv-rw19 gated handoff

Branch: `codex/cx-prover-rw-20261023`. Base: `d1351e0a2741079b6e206bfe2d84a0cd70706a3d`.

**Target not yet established. No new checked premise removal.** The restoration
flag remained absent throughout this continuation. Ruling (f) forbids every
host scope and local Lean compile. No infrastructure repair or toolchain
rebuild was attempted. Lean **0/100**, Kani **0/20** charged; next unused
Env-J ID **27700**. These budgets are unspent, not exhausted.

## Before/after statements

V164 checked before/after: **unchanged**, retaining
`source_law : ops.op223 = extracted` and
`context_identity : extracted = context.compress selected` in
`ProverRw18ContextJoin.callback`. The sibling at `40361dbd95` has no
`op223_source` theorem; V240 remains open.

Draft `ProverRw19P6ContextIdentity.identity` supplies the context identity
for the concrete previously extracted owned P6 reference, using the retained
arbitrary-slice theorem. Its caller consumers retain exactly
`P_source_p6 : ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)`.
This law is still unproved; no original whole-helper extraction is asserted.

V163 checked before/after: **OPEN**, missing the concrete mathematical
whole-model instance and both full observation equations. Draft audit
theorems derive the canonical successful audit `(16,10,true,true,true,true)`
from emitted guards, then derive the complete audit observation equation
from the byte equation for `attachAudit modelBytes`. This includes error,
failure and divergence. `attachAudit` is only a codec; `modelBytes` remains
a parameter, never defined as actual source output. The exact named
`P_proof_bytes` equation and reservation hypothesis are in
`ProverRw19CanonicalAuditRefinement.refinement`. Neither whole-fixture
equation is supplied. Endpoint premises are unchanged.

## Evidence and next deliverable

All nine rw19 modules are **unchecked drafts**. No new formal receipt or
`#print axioms` result exists; target/exit/wall/RSS/swap/revision/axioms are
therefore **N/A, not run**. `draft-preflight.json` is lexical checking only.
The frozen component manifest and audit were not changed or replayed.

`generator-check.json` records successful compile-free `--check`.
`p6-retained-provenance.json` verifies historical Rust, emission and prior
proof hashes, explicitly reusing their old receipts. `extractor-inventory.json`
records absent pinned Charon and surviving hashed Aeneas candidates under
`rng-extractor/`; no replacement frontend is built. `gate-checks.jsonl` and
`summary.json` retain the gate and budget state.

Next: read the restoration flag; compile the P6 identity smallest-first at
27700, then its consumers and the audit-value/source/data modules in the
README order. Repair only diagnosed proof failures. Re-freeze/audit once
focused targets pass. Then establish the exact P6 source law and construct
the mathematical whole-model byte function, proving its byte equation on
both release fixtures and arbitrary admitted inputs.

Proof-stage log (final evidence commit follows):

```
69e6be9746 Draft the successful audit invariant and its full observation transport
0488464c13 Carry the concrete P6 identity into the caller and retain both whole-model equations
6304fe427b Draft the concrete P6 compression context identity while the host gate is closed
```
