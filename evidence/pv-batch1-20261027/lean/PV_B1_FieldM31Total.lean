import PV_B1_FieldCTTotal
import PV_B1_ReadTotal
set_option autoImplicit false
namespace PV_B1_FieldM31Total
open Aeneas Aeneas.Std Result PV_B1_254
abbrev M := aspis_core.field.M31

theorem add (a b : M) : ∃ y, aspis_core.field.M31.add a b=ok y := by
  obtain ⟨y,hy⟩ := PV_B1_FieldCTTotal.add a b
  exact ⟨y,by simp only [aspis_core.field.M31.add,hy,bind_tc_ok]⟩

theorem sub (a b : M) : ∃ y, aspis_core.field.M31.sub a b=ok y := by
  obtain ⟨y,hy⟩ := PV_B1_FieldCTTotal.sub a b
  exact ⟨y,by simp only [aspis_core.field.M31.sub,hy,bind_tc_ok]⟩

theorem double (a : M) : ∃ y, aspis_core.field.M31.double a=ok y := by
  unfold aspis_core.field.M31.double
  exact add a a

theorem reduce64 (x : U64) : ∃ y, aspis_core.field.M31.reduce_u64 x=ok y := by
  obtain ⟨y,hy⟩ := PV_B1_FieldCTTotal.reduce64 x
  exact ⟨y,by simp only [aspis_core.field.M31.reduce_u64,aspis_core.field.reduce_u64,hy,bind_tc_ok]⟩

theorem mul (a b : M) : ∃ y, aspis_core.field.M31.mul a b=ok y := by
  unfold aspis_core.field.M31.mul aspis_core.field.reduce_u64
  simp only [lift,bind_tc_ok]
  apply PV_B1_ReadTotal.bind_total
  · exact PV_B1_FieldCTTotal.reduce64 _
  · intro y
    exact ⟨y,rfl⟩
#print axioms add
#print axioms sub
#print axioms double
#print axioms reduce64
#print axioms mul
end PV_B1_FieldM31Total
