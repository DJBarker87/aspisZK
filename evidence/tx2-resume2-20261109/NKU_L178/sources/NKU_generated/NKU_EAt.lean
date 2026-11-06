import NKU_InputAt
import NKK_ReadFrames
set_option autoImplicit false
noncomputable section
namespace NKU_EAt
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved NKU_InputAt
theorem returned (write : NKU.E → NKU.Decoded → NKU.Decoded)
 (s out : NKU.State) (cursor : Nat) (h : At s cursor) (fits : cursor+32≤1768)
 (actual : (NKU_FineRead.e write s).result=ok (.Ok ((),out))) :
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out (cursor+32) := by
 have fitsReader:=bound s cursor 32 h fits
 cases call : NIL_FreshOps.readE s.reader with
 | fail err =>
  simp only [NKU_FineRead.e,NJU_Log.erase_bind,recordE,NJU_Log.erase_record,call,bind_tc_fail] at actual
  cases actual
 | div =>
  simp only [NKU_FineRead.e,NJU_Log.erase_bind,recordE,NJU_Log.erase_record,call,bind_tc_div] at actual
  cases actual
 | ok pair =>
  rcases pair with ⟨inner,next⟩
  have fr:=NKK_ReadFrames.e s.reader next inner fitsReader call
  cases inner with
  | Err err =>
   simp only [NKU_FineRead.e,NJU_Log.erase_bind,recordE,NJU_Log.erase_record,call,bind_tc_ok,NKK_Try.branch,NJU_Log.erase_pure] at actual
   cases actual
  | Ok value =>
   simp only [NKU_FineRead.e,NJU_Log.erase_bind,recordE,NJU_Log.erase_record,call,bind_tc_ok,NKK_Try.branch,NJU_Log.erase_pure] at actual
   cases actual
   refine ⟨rfl,rfl,h.1,fr.1.trans h.2.1,?_⟩
   change next.at.val=cursor+32
   have advance:=fr.2
   have current:=h.2.2
   omega
theorem domain (write : NKU.E → NKU.Decoded → NKU.Decoded)
 (s : NKU.State) (cursor : Nat) (h : At s cursor) (fits : cursor+32≤1768) :
 NKK_LogClauses.Holds (Inside s.frame.checkpoint) (NKU_FineRead.e write s) := by
 unfold NKU_FineRead.e
 apply NKK_LogClauses.bind
 · apply NKK_LogClauses.record
   exact ⟨h.2.1,by rw [h.2.2,h.1];exact fits⟩
 · rintro ⟨reply,next⟩
   rw [NKK_Try.branch]
   cases reply <;> exact NKK_LogClauses.pure _ _
#print axioms returned
#print axioms domain
end NKU_EAt
