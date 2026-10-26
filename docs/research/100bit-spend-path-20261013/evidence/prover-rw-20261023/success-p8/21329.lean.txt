import R1Z.PV_CurrentSquare
import R1Z.ProverRwP7CompressPrimitives
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CurrentQuarticTotal
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev F := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square

theorem complex_add (a b : C) : ∃ c, PV_ProverRwP7CurrentComplexBridge.S.add a b = ok c := by
  rw [PV_ProverRwP7CurrentComplexBridge.add]
  obtain ⟨c,hc⟩ := ProverRwP6ComplexTotal.add (toC a) (toC b)
  exact ⟨fromC c,by rw [hc]; rfl⟩

theorem complex_mul (a b : C) : ∃ c, PV_ProverRwP7CurrentComplexBridge.S.mul a b = ok c := by
  rw [PV_ProverRwP7CurrentComplexBridge.mul]
  obtain ⟨c,hc⟩ := ProverRwP6ComplexTotal.mul (toC a) (toC b)
  exact ⟨fromC c,by rw [hc]; rfl⟩

theorem mul_by_r (a : C) : ∃ c, PV_CurrentQuarticBridge.S.mul_by_r a = ok c := by
  rw [PV_CurrentQuarticBridge.mul_by_r]
  obtain ⟨c,hc⟩ := ProverRwP6ComplexTotal.mul_by_r (toC a)
  exact ⟨fromC c,by rw [hc]; rfl⟩

theorem square (a : Q) : ∃ b, F a = ok b := by
  unfold F ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square
  apply ProverRwP6BindTotal.bind_total _ _ (PV_CurrentSquare.total _)
  intro c0
  apply ProverRwP6BindTotal.bind_total _ _ (PV_CurrentSquare.total _)
  intro c1
  apply ProverRwP6BindTotal.bind_total _ _ (mul_by_r _)
  intro c2
  apply ProverRwP6BindTotal.bind_total _ _ (complex_add _ _)
  intro c3
  apply ProverRwP6BindTotal.bind_total _ _ (complex_mul _ _)
  intro c4
  apply ProverRwP6BindTotal.bind_total _ _ (complex_add c4 c4)
  intro c5
  exact ⟨_,rfl⟩
#print axioms complex_add
#print axioms complex_mul
#print axioms mul_by_r
#print axioms square
end R1Z.PV_CurrentQuarticTotal
