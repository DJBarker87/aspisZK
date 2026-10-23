# H5 proof-friendly source adoption

Status: adopted on research after all final candidate gates passed and every
before/after source hash was checked. This is a working-source freeze, not a
release-security closure. Exact application receipt:
`../evidence/s9-h5-source-application-v1-20261023/application.json`.
The release security target is not yet established.

The owner explicitly authorized +12,214 CU per verification/settlement phase,
against the existing comparator. Select the callback-free H5 arithmetic and
tail scanner, plus the two ordered Core complement writes. This avoids
reintroducing the unproved Std Array.map refinement to save 872 CU, and removes
the actual fixed two-element iterator that previously required unsafe standard
library semantics. The spend relation, transparent proof format and admitted
transaction route do not change.

Before application, tracked `crates/`, `programs/`, root Cargo manifests/lock,
`.cargo/` and rust-toolchain.toml have no committed or working-tree delta
against source snapshot `76d32f4680a19b9609522decfdb6cdbc3e5e923b`.
This records the inspected project build-input scope; final dependency/toolchain
and artifact replay remain separate.

The isolated final candidate is ELF
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`.
Its six fixtures, strict stack audit and retained full-mask sample are recorded
in `../evidence/s9-h5-explicit-complements-feasibility-v1-20261023/`.
The maximum measured stage-1 increase is 12,214 CU; settlement increases reach
2,301 CU in the retained mask sample. Measurements are not a worst-case cost
proof. No deployment is part of this adoption.

The final-ELF readonly gate rejects all 13 mutations inside the verifier with
exact InvalidAccountData and unchanged protected negative states. Both controls
accept with the expected checkpoint/protected state and return bytes. The
historical diagnostic-log predicate was replaced in the harness by mandatory
actual-state and verifier-entry/consumption checks; negative rejection and
unchanged-state checks were retained. The rejected old-log run remains archived.
These are synthetic metadata cases, not a signed-state custody theorem.

## Source and evidence impact

Four files change: weights.rs, fast_pairing.rs, r1_pool_adapter_owned.rs and
Core state_only_prefix.rs. The actual caller r1_pool_adapter.rs and fast_dots.rs
remain byte-identical. The adoption review packet must retain exact before and
after file hashes, every changed declaration span, and the full patch. All before hashes matched the shared worktree, the patch applied cleanly, and
all four after hashes match the measured candidate. Unrelated concurrent proof
work was retained.

The current extracted constructor, factor loops, scalar helper, tensor and
actual-pair source cuts already target H5 bodies. Their focused value-level
proofs remain applicable by exact source-span pins, not by function names.
The new Core helper body matches the extracted V3 two-write helper exactly.
The scanner theorem proves all-input pure-result equivalence with the actual
SDK error type, including every rejection. These facts do not supply an
unproved whole-caller or adaptive-oracle simulation.

Changed arithmetic bodies reopen their S3/S4/S5/S8/S9 body and dependency
pins, including the canonical dot operations reached by S4; scanner and
caller-containing cones require their relevant S1/S4 pins to be assessed. The Core caller cone also needs its transitive source pin updated.
S10 must inventory the actual final source and emitted artifacts coherently.
The previous S10 inventory is explicitly incomplete and is not made complete
by a textual declaration list. Historical whole-file or ELF identities must
not be relabelled as this artifact.

Reuse unchanged decoder/arithmetic/field algebra, generic loop invariants,
unchanged caller guard SDK differential tests, and exact constructor/circle
source-cut proofs with their existing receipts. Rerun only genuinely affected
native Core/weights/shared suites and final-ELF readonly gates. The focused
proof queue continues on scalar-factor decoded values and actual field/dot
reader correspondence while adoption gates finish. The coherent release
closure replay comes after the remaining focused source/security obligations,
not as a substitute for them.

## Remaining security work

Full weighted-dot/shared-high/grouped-inactive/final-kappa pairing equations,
finish relation composition, the relevant source/runtime/oracle transports,
final source/artifact correspondence, and the global soundness experiment
remain open. Standard Aeneas Box erasure is an explicit translator trust
boundary, not a new allocator axiom or a physical allocation theorem.
The authoritative security contract and gap map retain precedence.
