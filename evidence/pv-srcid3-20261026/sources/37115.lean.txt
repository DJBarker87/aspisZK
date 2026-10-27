import R1Z.PV_Src_PortReduce

/-! Complete Result source-to-copy equations for the nonlinear scalar layer.
Arguments are arbitrary U32 values; no field canonicality is assumed. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortMultiply
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort

theorem multiply (a b : U32) :
    aspis_core.field.M31.mul a b = R0PoseidonCopy.m31_mul a b := by
  unfold aspis_core.field.M31.mul R0PoseidonCopy.m31_mul
  simp only [lift,bind_tc_ok]
  change aspis_core.field.M31.reduce_u62 _ = _
  exact PV_Src_PortReduce.modulo _

theorem power (a : U32) : poseidon2.pow5 a = R0PoseidonCopy.pow5 a := by
  unfold poseidon2.pow5 R0PoseidonCopy.pow5
  simp only [multiply]

#print axioms multiply
#print axioms power
end R1Z.PV_Src_PortMultiply
