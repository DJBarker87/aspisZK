import R1Z.PV_RunJoin_NativePowerScalar66
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePowerMTotal66
open Aeneas Aeneas.Std Result PV_B1_254
theorem reduce64 (x : U64) : ∃ z, aspis_core.field.M31.reduce_u64 x=ok z := by
  simp only [aspis_core.field.M31.reduce_u64,aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,lift,bind_tc_ok,PV_RunJoin_NativePowerScalar66.subtract]
  exact ⟨_,rfl⟩
#print axioms reduce64
theorem add (x y : U32) : ∃ z, aspis_core.field.M31.add x y=ok z := by
  simp only [aspis_core.field.M31.add,aspis_core.field.ct.add,lift,bind_tc_ok,PV_RunJoin_NativePowerScalar66.subtract]
  exact ⟨_,rfl⟩
#print axioms add
theorem sub (x y : U32) : ∃ z, aspis_core.field.M31.sub x y=ok z := by
  simp only [aspis_core.field.M31.sub,aspis_core.field.ct.sub,lift,bind_tc_ok,PV_RunJoin_NativePowerScalar66.subtract]
  exact ⟨_,rfl⟩
#print axioms sub
theorem mul (x y : U32) : ∃ z, aspis_core.field.M31.mul x y=ok z := by
  unfold aspis_core.field.M31.mul
  simp only [lift,bind_tc_ok]
  obtain ⟨z,hz⟩ := reduce64 (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))
  exact ⟨z,hz⟩

theorem double (x : U32) : ∃ z, aspis_core.field.M31.double x=ok z := add x x
#print axioms mul
#print axioms double
end R1Z.PV_RunJoin_NativePowerMTotal66
