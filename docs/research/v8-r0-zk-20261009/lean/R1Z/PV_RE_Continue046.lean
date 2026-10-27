import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue046
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

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (h1 := h1) (padding := padding) =
      (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows >>= fun out => continueAfter (h1 := h1) (padding := padding) out) := by
  rw [aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) (out : Payload (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows))
    (h : (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows) = .ok out) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (h1 := h1) (padding := padding) = continueAfter (h1 := h1) (padding := padding) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) (e : Error)
    (h : (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows) = .fail e) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (h1 := h1) (padding := padding) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31)
    (h : (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows) = .div) :
    aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (h1 := h1) (padding := padding) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue046
