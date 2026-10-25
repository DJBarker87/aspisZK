# Stage 1: inventory

Established by source inspection: complete selected Pool dispatch classification,
separate verifier release dispatch classification, one active writer of each
checkpoint kind, helper/cross-role/CPI/rollback/assignment boundary inventory.
Exact claim and file:line evidence: design/POOL-LIFECYCLE-SCOPE-20261026.md,
rows V0–V3, P0–P11, H1–H2, C1–C2, R1–R4. No accepted attacker-chosen
checkpoint write found. No formal universal closure claimed.

All inherited build-manifest repository inputs compare equal to current bytes:
133 Pool, 132 default verifier, 132 devnet verifier. ELF hashes/sizes reused
from Low2 artifacts; no binary rebuilt, read from disk or deployed-code fetched.
No shipped changes trigger a rebuild. Full manifest/refinement is not replayed.

PoolS_surface-scan.json is a reproducible lexical scope measurement, not a
Rust parser/callgraph/feature evaluator. It deliberately records some test-only
helpers before final test modules and feature-off functions. Human inventory
classifies those. No new compiler invocation: Lean0/20, Kani0/10. Formal attempt
exit/wall/RSS/swap/axioms: not applicable. Source hashes and revision in Stage0.
No assumptions discharged at the global theorem; SDK/runtime/extraction and
initial-state/deployment association remain explicit. Next deliverable: exact
property and costed choice of proof scope.
