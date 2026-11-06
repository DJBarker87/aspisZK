import NKU_InputAt
import NKK_NativeRaw
set_option autoImplicit false
noncomputable section
namespace NKU_RawAt
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved NKU_InputAt
/-- Complete SAME-argument local success/frame, used inside an actual entered
branch. Source lemma is generic; native parent uses only4 and32. -/
theorem total (n : Usize) (write : Array U8 n → NKU.Decoded → NKU.Decoded)
 (s : NKU.State) (cursor : Nat) (h : At s cursor) (fits : cursor+n.val≤1768) :
 ∃ out,(NKU_FineRead.raw n write s).result=ok (.Ok ((),out)) ∧
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out (cursor+n.val) := by
 obtain ⟨b,next,cut,call⟩:=NKK_NativeRaw.one n s.reader (bound s cursor n.val h fits)
 refine ⟨{s with reader := next,decoded := write b s.decoded},?_,rfl,rfl,?_,?_,?_⟩
 · simp only [NKU_FineRead.raw,NJU_Log.erase_bind,recordRaw,NJU_Log.erase_record,call,bind_tc_ok,NJU_Log.erase_pure]
 · exact h.1
 · exact cut.2.2.trans h.2.1
 · change next.at.val=cursor+n.val
   have advance:=cut.2.1
   have current:=h.2.2
   omega
theorem domain (n : Usize) (write : Array U8 n → NKU.Decoded → NKU.Decoded)
 (s : NKU.State) (cursor : Nat) (h : At s cursor) (fits : cursor+n.val≤1768) :
 NKK_LogClauses.Holds (Inside s.frame.checkpoint) (NKU_FineRead.raw n write s) := by
 unfold NKU_FineRead.raw
 apply NKK_LogClauses.bind
 · apply NKK_LogClauses.record
   exact ⟨h.2.1,by rw [h.2.2,h.1];exact fits⟩
 · rintro ⟨b,next⟩
   exact NKK_LogClauses.pure _ _
#print axioms total
#print axioms domain
end NKU_RawAt
