import R1Z.PV_RDB2E_FallbackBlock
import R1Z.PV_RDB2E_FallbackSchedule
import R1Z.PV_RDB2E_FallbackRound
import R1Z.PV_RDB2E_FallbackArray4

section
-- Unchanged source component R1Z.PV_CBL_FallbackBlockLinks
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackBlockLinks
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shl_eq (v : A4) (o : U32) :
    PV_CBL_FallbackBlock.sha_fallback_reference.shl v o =
    PV_CBL_FallbackSchedule.sha_fallback_reference.shl v o := rfl
theorem shr_eq (v : A4) (o : U32) :
    PV_CBL_FallbackBlock.sha_fallback_reference.shr v o =
    PV_CBL_FallbackSchedule.sha_fallback_reference.shr v o := rfl
theorem or_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.or a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.or a b := rfl
theorem xor_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.xor a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.xor a b := rfl
theorem add_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.add a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.add a b := rfl
theorem load_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256load a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load a b := rfl
theorem msg2_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256msg2 a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg2 a b := rfl
theorem sigma_eq (a : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256msg1.sigma0x4 a =
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1.sigma0x4 a := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_reference.sha256msg1.sigma0x4,
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1.sigma0x4,
    shl_eq,shr_eq,or_eq,xor_eq]
theorem msg1_eq (a b : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256msg1 a b =
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1 a b := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_reference.sha256msg1,
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1,load_eq,sigma_eq,add_eq]
theorem schedule_eq (a b c d : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule a b c d =
    PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule a b c d := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_reference.schedule,
    PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule,
    PV_CBL_FallbackSchedule.sha_fallback_reference.schedule,msg1_eq,load_eq,add_eq,msg2_eq]
theorem round_eq (a b w : A4) :
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 a b w =
    PV_CBL_FallbackRound.sha_fallback_reference.sha256_digest_round_x2 a b w := rfl
#print axioms shl_eq
#print axioms shr_eq
#print axioms or_eq
#print axioms xor_eq
#print axioms add_eq
#print axioms load_eq
#print axioms msg2_eq
#print axioms sigma_eq
#print axioms msg1_eq
#print axioms schedule_eq
#print axioms round_eq
end R1Z.PV_CBL_FallbackBlockLinks

end
