import R1Z.PV_Join_OwnedScalarBridge5
import R1Z.PV_Join_ReducerCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_OwnedScalarCanonical5
open Aeneas Aeneas.Std Result PV_Join_Canonical5

theorem mul (a b : U32) :
    ∃ z, PV_Join_Direct5Source.aspis_core.field.M31.mul a b = .ok z ∧ M z := by
  rw [PV_Join_OwnedScalarBridge5.mul]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.mul_exact a b
  exact ⟨z,hz,hc⟩
theorem add (a b : U32) (ha : M a) (hb : M b) :
    ∃ z, PV_Join_Direct5Source.aspis_core.field.M31.add a b = .ok z ∧ M z := by
  rw [PV_Join_OwnedScalarBridge5.add]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.add_exact a b ha hb
  exact ⟨z,hz,hc⟩
theorem sub (a b : U32) (ha : M a) (hb : M b) :
    ∃ z, PV_Join_Direct5Source.aspis_core.field.M31.sub a b = .ok z ∧ M z := by
  rw [PV_Join_OwnedScalarBridge5.sub]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.sub_exact a b ha hb
  exact ⟨z,hz,hc⟩
theorem double (a : U32) (ha : M a) :
    ∃ z, PV_Join_Direct5Source.aspis_core.field.M31.double a = .ok z ∧ M z := by
  exact add a a ha ha

#print axioms mul
#print axioms add
#print axioms sub
#print axioms double
end R1Z.PV_Join_OwnedScalarCanonical5
