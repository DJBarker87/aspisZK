# Forest group candidate

New module: crates/aspis-r1-cost-probe/src/host_forest.rs. Gate in lib.rs: `#[cfg(feature = "prover")] pub mod host_forest;`. The default release program depends on `optimized-terminal,program-build`, which do not enable prover. The devnet build uses the same crate feature edge. Pool and Registry do not depend on this module. No original statement/core function is edited.

Copies: legacy row schedule -> forest schedule -> sorted active rows -> active/inactive masks; legacy registry -> translated forest registry. Fixed Copy carriers contain 136 schedule/registry slots and an explicit logical length. Active rows use 214 slots and a logical length. Endpoint capacity checks retain their producer-before-consumer order. A fixed carrier's bounds and successful logical lengths remain formal obligations, not inferred from native success.

Redirected chains:
- host_semantic::no_pole -> host_forest::active masks -> active rows -> forest schedule -> legacy schedule;
- host_semantic::lean_copy_row_values -> host_forest::forest registry -> legacy registry and forest schedule;
- host_semantic::{build_pair_forest,build_pair_forest_with_material} -> copied helper builder -> copied row builder -> forest registry (the actual public function names are in the diff).

The copied row/helper caller wrappers preserve the original Vec return carriers and original tuple/weight semantics, including first-zero-weight slot placement. The roots selected for extraction are the fixed-carrier inventory/registry functions, not these allocating wrappers. No change to the zero-weight behavior is authorized. Public terminal chains still use their original statement implementation until the later terminal group.

Validation status at source freeze: first host optimized cargo check failed because the sparse host snapshot lacked the original include file refine/diffharness/tests/glue_gen.rs; the include is restored byte-for-byte, a changed compiler input. No Lean attempt charged. ELF checks, projections and source-law proof gates remain pending; this is not adoption evidence.
