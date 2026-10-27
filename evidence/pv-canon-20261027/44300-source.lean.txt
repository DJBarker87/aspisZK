import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_cnew (x y : U32) (hx : M x) (hy : M y) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.new x y = .ok z ∧ C z :=
  ⟨⟨x,y⟩,rfl,hx,hy⟩
 theorem current_qzero : Q ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO := by
  rw [ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO]
  exact ⟨⟨zero,zero⟩,⟨zero,zero⟩⟩
 theorem current_qone : Q ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE := by
  rw [ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE]
  exact ⟨⟨one,zero⟩,⟨zero,zero⟩⟩
 theorem sample_m31 (i : U32) (hi : i.val < 28) : M i := by
  unfold M; omega
 theorem half_constant : M (1073741824#u32) := by change 1073741824 < 2147483647; omega
 theorem quarter_constant : M (536870912#u32) := by change 536870912 < 2147483647; omega
#print axioms current_cnew
#print axioms current_qzero
#print axioms current_qone
#print axioms sample_m31
#print axioms half_constant
#print axioms quarter_constant
end R1Z.PV_Canon
