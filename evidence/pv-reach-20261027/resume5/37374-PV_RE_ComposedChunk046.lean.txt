import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix046
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1`.
Recursive calls remain the original extracted calls. -/
def continueAfter (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) (out : Payload (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows)) : Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × (Slice
    aspis_core.field.QM31)) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    aspis_prover.state_only_hiding.apply_h1_padding_mask_for_active h1 padding
      val
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
    ok (r1, h1)


end R1Z.PV_RE_ComposedSuffix046
pv_composed_source_contexts ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix046.continueAfter
