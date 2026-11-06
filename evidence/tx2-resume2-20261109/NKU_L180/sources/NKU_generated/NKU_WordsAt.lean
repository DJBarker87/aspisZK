import NKU_RawAt
import NKU_FineWords
import NKK_RawChain
import NKK_RawResult
set_option autoImplicit false
noncomputable section
namespace NKU_WordsAt
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved NKU_InputAt
/-- Domain and immutable frame of the actual one-state word fold. Only the
8/8/6 literal native windows are credited, not arbitrary new Rust widths. -/
theorem total (n : Nat) (s : NKU.State) (cursor : Nat) (h : At s cursor)
 (fits : cursor+4*n≤1768) :
 ∃ out,(NKU_FineWords.run n s).result=ok (.Ok ((),out)) ∧
 out.frame=s.frame ∧ out.owned=s.owned ∧ At out (cursor+4*n) := by
 have readBound : s.reader.at.val+4*n≤s.reader.bytes.val.length := by rw [h.2.1,h.1,h.2.2];exact fits
 obtain ⟨bs,last,chain,size,call⟩:=NKK_NativeRaw.read_chain 4#usize n s.reader readBound
 have literal : (NKK_RawPrefix.literal 4#usize n s.reader).result=ok (bs,last) :=
  (NKK_RawResult.source 4#usize n s.reader).trans call
 refine ⟨NKU_FineWords.post s bs last,?_,rfl,rfl,h.1,?_,?_⟩
 · rw [NKU_FineWords.installed]
   simp only [NKU_FineWords.source,NJU_Log.erase_bind,literal,bind_tc_ok,NJU_Log.erase_pure]
 · exact (NKK_NativeRaw.backing chain).trans h.2.1
 · change last.at.val=cursor+4*n
   have advance:=NKK_NativeRaw.advance chain
   change last.at.val=s.reader.at.val+4*bs.length at advance
   rw [size] at advance
   have current:=h.2.2
   omega
#print axioms total
end NKU_WordsAt
