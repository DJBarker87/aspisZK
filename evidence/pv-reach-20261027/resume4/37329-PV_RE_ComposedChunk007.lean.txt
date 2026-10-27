import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix007
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows`.
Recursive calls remain the original extracted calls. -/
def continueAfter  (out : Payload (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1)) : Result (core.result.Result (Array Bool 1024#usize)
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) := do
  let r := out
  let r1 ←
    core.result.Result.map
      aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows.closure.Insts.CoreOpsFunctionFnOnceTupleVecU16ArrayBool1024
      r ()
  core.result.Result.map_err
    aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1StateOnlyMaskBuildError
    r1 ()


end R1Z.PV_RE_ComposedSuffix007
pv_composed_source_contexts ProverRwFull.aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix007.continueAfter
