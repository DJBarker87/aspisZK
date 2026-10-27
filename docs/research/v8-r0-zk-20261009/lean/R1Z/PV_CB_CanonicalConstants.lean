import R1Z.PV_CB_CanonicalTower
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalConstants
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_CanonicalTower.Q

theorem zero : PV_CB_CanonicalTower.Valid
    ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO := by
  unfold ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
  change ((0#u32).val < AspisCircleGroupOrder.P ∧ (0#u32).val < AspisCircleGroupOrder.P) ∧
    ((0#u32).val < AspisCircleGroupOrder.P ∧ (0#u32).val < AspisCircleGroupOrder.P)
  exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩

theorem one : PV_CB_CanonicalTower.Valid
    ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE := by
  unfold ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE
  change ((1#u32).val < AspisCircleGroupOrder.P ∧ (0#u32).val < AspisCircleGroupOrder.P) ∧
    ((0#u32).val < AspisCircleGroupOrder.P ∧ (0#u32).val < AspisCircleGroupOrder.P)
  exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
#print axioms zero
#print axioms one
end R1Z.PV_CB_CanonicalConstants
