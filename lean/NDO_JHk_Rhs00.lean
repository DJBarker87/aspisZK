import NDO_JHk_Line00
import RPt_JFq_Rho
import RPt_JFq_Rhs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Rhs00
abbrev FE := AspisWideTower.WideExact
abbrev K := OraclePortCheckpointAbiC5.K
def rhs : FE := ⟨⟨⟨693198916,639986381⟩,⟨1864761200,1927747454⟩⟩,⟨⟨2142802787,1648541873⟩,⟨1657099671,1353897268⟩⟩⟩
def power : K := ⟨⟨1497225503,277942247⟩,⟨877802089,1707877402⟩⟩
/-- One exact contribution, never an unfolded query recurrence. -/
theorem rhs_step : (0 : FE)+LiteralOpeningView.eK (1 : K)*JHk_Line00.value=rhs := by
  rw [map_one,one_mul,zero_add]
  rfl
#print axioms rhs_step
theorem power_step : (1 : K)*CheckpointBytes5Output.ofK JFq_Rho.scalar=power := by
  rw [one_mul]
  rfl
#print axioms power_step
end AspisR1.JHk_Rhs00
end
