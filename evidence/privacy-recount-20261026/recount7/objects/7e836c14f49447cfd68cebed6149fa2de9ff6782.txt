import R1Z.PV_Src_PortField
import R1Z.PV_RunJoin_ValidationScalar16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_Subtraction31
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderForestAdmissionPort
variable {K : Type} [Field K] [CharP K 2147483647]

theorem source (a b : U32) : aspis_core.field.M31.sub a b = R0BlockCopies.m31_sub a b := by
  simp only [aspis_core.field.M31.sub,R0BlockCopies.m31_sub,
    aspis_core.field.P,R0BlockCopies.P,lift,bind_tc_ok]
#print axioms source

theorem field (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ z, aspis_core.field.M31.sub a b = ok z ∧ z.val < 2147483647 ∧
      liftU (K := K) z = liftU a - liftU b := by
  obtain ⟨z,hz,hv⟩ := m31_sub_spec_wide a b ha hb
  refine ⟨z,(source a b).trans hz,?_,?_⟩
  · rw [hv]; split_ifs <;> omega
  · unfold liftU
    rw [hv]
    exact lift_m31_sub a.val b.val hb
#print axioms field
end R1Z.PV_RunJoin_Subtraction31
