import NIS_ErrorJoin
set_option autoImplicit false
noncomputable section
namespace NLQ_ErrorMapper
open Aeneas Aeneas.Std Result
/-- The closed error row's returning value, at the SAME complete logging
call. This is a local domain lemma, not an assertion that logging returns. -/
theorem returning {S : Type} (emit : String → S → Result S)
 (e : NIJ_ErrorJoin.E) (s post : S) (reply : NIJ_ErrorJoin.PE)
 (returned : NIJ_ErrorJoin.run emit e s = .ok (reply,post)) :
 reply = .InvalidInstructionData := by
 unfold NIJ_ErrorJoin.run at returned
 cases h : emit (NIJ_ErrorJoin.formatted e) s with
 | fail err => simp only [h,bind_tc_fail] at returned; cases returned
 | div => simp only [h,bind_tc_div] at returned; cases returned
 | ok after =>
   simp only [h,bind_tc_ok] at returned
   exact (congrArg Prod.fst (Result.ok.inj returned)).symm
/-- Byte identity and abort prefix are reused from the actual CLOSED row;
they are NOT a full external/account/allocator post-frame theorem. -/
theorem label (e : NIJ_ErrorJoin.E) :
 NIJ_ErrorJoin.formatted e = NGL_ErrorModel.message e := NIJ_ErrorJoin.bytes e
#check @returning
#print axioms returning
#print axioms label
end NLQ_ErrorMapper
