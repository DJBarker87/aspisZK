import R1Z.PV_Canon_Carrier
import R1Z.ProverCommitInverse48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
/-- Successful fixed-chain owned inverse returns canonical; zero failure is
not repaired or assumed away. Its installed source association remains separate. -/
theorem inverse_owned_canonical (x y : U32)
    (h : ProverCommitInverse48.inverse_owned x = .ok y) : M y := by
  rw [ProverCommitInverse48.inverse_result] at h
  simp only [lift,bind_tc_ok] at h
  split at h
  · cases h
  · cases h
    exact ProverCommitInverse48.inverse_canonical x
#print axioms inverse_owned_canonical
end R1Z.PV_Canon
