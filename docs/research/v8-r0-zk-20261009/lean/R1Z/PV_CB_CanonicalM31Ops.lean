import R1Z.PV_CB_CanonicalM31
import R1Z.ProverCommitM31Ops48
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalM31Ops
open Aeneas Aeneas.Std Result PV_CB_CanonicalM31

theorem add (a b : U32) (ha : Valid a) (hb : Valid b) :
    ∃ value, ProverRwP7CurrentBaseBridge.S.add a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitM31Ops48.add_exact a b ha hb
  exact ⟨value,(ProverRwP7CurrentBaseBridge.add a b).trans hvalue,hcanonical⟩

theorem sub (a b : U32) (ha : Valid a) (hb : Valid b) :
    ∃ value, ProverRwP7CurrentBaseBridge.S.sub a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitM31Ops48.sub_exact a b ha hb
  exact ⟨value,(ProverRwP7CurrentBaseBridge.sub a b).trans hvalue,hcanonical⟩

theorem double (a : U32) (ha : Valid a) :
    ∃ value, ProverRwP7CurrentBaseBridge.S.double a = ok value ∧ Valid value := by
  simpa only [ProverRwP7CurrentBaseBridge.S.double,
    ProverRwP7CurrentFieldSource.aspis_core.field.M31.double] using add a a ha ha
#print axioms add
#print axioms sub
#print axioms double
end R1Z.PV_CB_CanonicalM31Ops
