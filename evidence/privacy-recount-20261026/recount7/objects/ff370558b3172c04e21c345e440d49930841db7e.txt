import R1Z.PV_Src_PortReduce
import R0Z.NodeRefine

/-! Canonical-input arithmetic for the actual hash's wrapping addition.
No arbitrary-word modular-add claim is made. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortAddition
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort

theorem source (a b : U32) :
    aspis_core.field.M31.add a b = R0BlockCopies.m31_add a b := by
  simp only [aspis_core.field.M31.add,R0BlockCopies.m31_add,
    aspis_core.field.P,R0BlockCopies.P,lift,bind_tc_ok]

theorem canonical (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ z, aspis_core.field.M31.add a b = ok z ∧
      z.val = (a.val+b.val)%2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z,hz,hv⟩ := m31_add_spec a b ha hb
  refine ⟨z,by rw [source];exact hz,?_,?_⟩
  · rw [hv]
    split
    · next h => rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  · rw [hv]
    split <;> omega

#print axioms source
#print axioms canonical
end R1Z.PV_Src_PortAddition
