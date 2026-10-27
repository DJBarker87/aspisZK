import R1Z.PV_CB_CanonicalTower
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalQuartic
open Aeneas Aeneas.Std Result PV_CB_CanonicalTower

theorem add (a b : Q) (ha : Valid a) (hb : Valid b) :
    ∃ value, PV_CB_CurrentQuartic.S.add a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeQ48.add (old a) (old b) ha hb
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentQuartic.add,source,source,hvalue]
  rfl

theorem mul (a b : Q) (ha : Valid a) (hb : Valid b) :
    ∃ value, PV_CB_CurrentQuartic.S.mul a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeQ48.mul (old a) (old b) ha hb
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentQuartic.mul,source,source,hvalue]
  rfl
#print axioms add
#print axioms mul
end R1Z.PV_CB_CanonicalQuartic
