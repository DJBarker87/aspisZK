import R1Z.PV_RDB2E_FallbackTotal
import R1Z.PV_RDB2E_FallbackRoundComplete
import R1Z.PV_RDB2E_FallbackScheduleShape
import R1Z.PV_RDB2E_FallbackBlockSwap
import R1Z.PV_RDB2E_FallbackLanes

section
-- Unchanged source component R1Z.PV_CBL_FallbackHelpersTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackHelpersTotal
open PV_CBL_FallbackArray4 PV_CBL_FallbackRoundTotal PV_CBL_FallbackTotal
set_option autoImplicit false
theorem add (a b : A4) : Total (PV_CBL_FallbackBlock.sha_fallback_reference.add a b) := by
  have h := PV_CBL_FallbackLaneAdd.shape a.val[0]! a.val[1]! a.val[2]! a.val[3]!
    b.val[0]! b.val[1]! b.val[2]! b.val[3]!
  simp only [pack_eta] at h
  rw [PV_CBL_FallbackBlockLinks.add_eq]
  exact ⟨_,h⟩
theorem swap (a : A4) : Total (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap a) := by
  have h := PV_CBL_FallbackBlockSwap.shape a.val[0]! a.val[1]! a.val[2]! a.val[3]!
  simp only [pack_eta] at h
  exact ⟨_,h⟩
theorem round (a b w : A4) :
    Total (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 a b w) := by
  rw [PV_CBL_FallbackBlockLinks.round_eq]
  exact PV_CBL_FallbackRoundComplete.total a b w
theorem schedule (a b c d : A4) : Total (PV_CBL_FallbackBlock.sha_fallback_reference.schedule a b c d) := by
  have h := PV_CBL_FallbackScheduleShape.shape a.val[0]! a.val[1]! a.val[2]! a.val[3]!
    b.val[0]! b.val[1]! b.val[2]! b.val[3]! c.val[0]! c.val[1]! c.val[2]! c.val[3]!
    d.val[0]! d.val[1]! d.val[2]! d.val[3]!
  simp only [pack_eta] at h
  rw [PV_CBL_FallbackBlockLinks.schedule_eq]
  exact ⟨_,h⟩
#print axioms add
#print axioms swap
#print axioms round
#print axioms schedule
end R1Z.PV_CBL_FallbackHelpersTotal

end
