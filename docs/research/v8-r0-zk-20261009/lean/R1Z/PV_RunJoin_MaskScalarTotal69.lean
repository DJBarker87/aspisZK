import PV_B3_Install117
import R1Z.ProverRwP6BindTotal
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskScalarTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117

theorem add (a b : U32) : ∃ c, aspis_core.field.M31.add a b=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem sub (a b : U32) : ∃ c, aspis_core.field.M31.sub a b=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem mul (a b : U32) : ∃ c, aspis_core.field.M31.mul a b=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem reduce (a : U64) : ∃ c, aspis_core.field.M31.reduce_u64 a=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem neg (a : U32) : ∃ c, aspis_core.field.M31.neg a=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem double (a : U32) : ∃ c, aspis_core.field.M31.double a=ok c := by
  simp only [aspis_core.field.M31.add,aspis_core.field.M31.sub,aspis_core.field.M31.mul,
    aspis_core.field.M31.neg,aspis_core.field.M31.double,aspis_core.field.M31.reduce_u64,
    aspis_core.field.reduce_u64,aspis_core.field.ct.reduce64,aspis_core.field.ct.subtract_p,
    aspis_core.field.ct.add,aspis_core.field.ct.sub,aspis_core.field.ct.neg,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

#print axioms add
#print axioms sub
#print axioms mul
#print axioms reduce
#print axioms neg
#print axioms double
end R1Z.PV_RunJoin_MaskScalarTotal69
