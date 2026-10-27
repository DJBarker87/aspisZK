import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix046
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


end R1Z.PV_RE_NoCatchSuffix046
pv_no_catch_binds ProverRwFull.aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix046.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix047
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.Commitment.fill_opening`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (pvBoundValue : Payload (host_commitment.fill_opening_values self u out.values 0#usize)) : Result aspis_core.r0.wire.FibreOpening := do
  let a := pvBoundValue
  let path ← host_commitment.opening_path self.time
  let a1 := Array.repeat 32#usize 0#u8
  let a2 := Array.repeat 7#usize a1
  let a3 := Array.repeat 6#usize a2
  let a4 ← Array.update out.paths path a3
  ok { values := a, paths := a4 }


end R1Z.PV_RE_NoCatchSuffix047
pv_no_catch_binds ProverRwFull.host_commitment.Commitment.fill_opening
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix047.continueAfter
