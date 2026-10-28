import R1Z.PV_RunJoin_DigestCanonical16
import R1Z.PV_Src_AdmissionScalar
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ValidationScalar16
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort

theorem sub_self (a : U32) (ha : a.val < 2147483647) :
    aspis_core.field.M31.sub a a = ok 0#u32 := by
  with_unfolding_all exact PV_Src_AdmissionScalar.sub_self a ha

theorem mul_zero (a : U32) : aspis_core.field.M31.mul 0#u32 a = ok 0#u32 := by
  with_unfolding_all exact PV_Src_AdmissionScalar.mul_zero a
#print axioms sub_self
#print axioms mul_zero
end R1Z.PV_RunJoin_ValidationScalar16
