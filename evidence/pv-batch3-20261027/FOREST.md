# Forest group candidate

New module: crates/aspis-r1-cost-probe/src/host_forest.rs. Gate in lib.rs: `#[cfg(feature = "prover")] pub mod host_forest;`. The default release program depends on `optimized-terminal,program-build`, which do not enable prover. The devnet build uses the same crate feature edge. Pool and Registry do not depend on this module. No original statement/core function is edited.

Copies: legacy row schedule -> forest schedule -> sorted active rows -> active/inactive masks; legacy registry -> translated forest registry. Fixed Copy carriers contain 136 schedule/registry slots and an explicit logical length. Active rows use 214 slots and a logical length. Endpoint capacity checks retain their producer-before-consumer order. A fixed carrier's bounds and successful logical lengths remain formal obligations, not inferred from native success.

Redirected chains:
- host_semantic::no_pole -> host_forest::active masks -> active rows -> forest schedule -> legacy schedule;
- host_semantic::lean_copy_row_values -> host_forest::forest registry -> legacy registry and forest schedule;
- host_semantic::{build_pair_forest,build_pair_forest_with_material} -> copied helper builder -> copied row builder -> forest registry (the actual public function names are in the diff).

The copied row/helper caller wrappers preserve the original Vec return carriers and original tuple/weight semantics, including first-zero-weight slot placement. The roots selected for extraction are the fixed-carrier inventory/registry functions, not these allocating wrappers. Op224 will include its own separately extracted Drop-free row/helper implementation in the following group; this group’s copied allocating wrapper only redirects the registry caller chain. No change to the zero-weight behavior is authorized. Public terminal chains still use their original statement implementation until the later terminal group.

Validation status at source freeze: first host optimized cargo check failed because the sparse host snapshot lacked the original include file refine/diffharness/tests/glue_gen.rs; the include is restored byte-for-byte, a changed compiler input. No Lean attempt charged. ELF checks, projections and source-law proof gates remain pending; this is not adoption evidence.

## Completed caller placement

The shared module now lives at crates/aspis-prover/src/host_forest.rs under `#[cfg(feature="prover")]`. The cost-probe module is a gated re-export, and its prover feature forwards aspis-prover/prover. New feature prover has no release-program enabling edge. The masking/entropy/rank host modules select the copies through cfg-gated imports; their non-prover imports select the untouched originals.

Op132 additionally copies relation-free mask-cell generation into a fixed 3,803-cell carrier. Allocation adapters materialize exactly the logical slices for existing masking/rank callers. Host prover::prove_masked_with_attempt and ReservedStateOnlyAttemptSecrets' mask helpers now use the copied masks. The source-job authority identifies op132=cells,133=active rows,134=active masks; the historical PV_Op134 inventory naming must not be mistaken for this operation-number mapping.

The initial partial forest snapshot passed all three ELF pins at host forest-elf-02. Initial forest-elf-01 failed rustc codegen thread creation (WouldBlock, TasksMax64); forest-elf-02 changes only CPU affinity to 0-3, keeping all caps/toolchain/commands. The completed caller snapshot requires a fresh gate; no partial pin result is attributed to it.
