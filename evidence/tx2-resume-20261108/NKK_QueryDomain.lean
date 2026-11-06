import NKK_QueryStage
import NKK_RawResult
import NKK_RawSlots
set_option autoImplicit false
noncomputable section
namespace NKK_QueryDomain
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_NativeRaw

/-- Actual successful native query windows determine the SAME ordered words,
backing and cursor; the bound is the actual caller's local Reader fact. -/
theorem eight (r : Reader) (block : Fin 2)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=320+32*block.val) :
 ∃ (qs : List U32) (last : Reader), qs.length=8 ∧
 (NKK_QueryStage.model8 r).result=ok (qs,last) ∧
 last.bytes=r.bytes ∧ last.at.val=352+32*block.val := by
 obtain ⟨bs,last,chain,size,run,frame,advance⟩:=NKK_RawSlots.query8 r block length cursor
 refine ⟨bs.map core.num.U32.from_le_bytes,last,?_,?_,frame,advance⟩
 · simpa only [List.length_map] using size
 · simp only [NKK_QueryStage.model8,NJU_Log.erase_bind,NKK_RawResult.source,run,NJU_Log.erase_pure]
   all_goals rfl

theorem six (r : Reader)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=384) :
 ∃ (qs : List U32) (last : Reader), qs.length=6 ∧
 (NKK_QueryStage.model6 r).result=ok (qs,last) ∧
 last.bytes=r.bytes ∧ last.at.val=408 := by
 obtain ⟨bs,last,chain,size,run,frame,advance⟩:=NKK_RawSlots.query6 r length cursor
 refine ⟨bs.map core.num.U32.from_le_bytes,last,?_,?_,frame,advance⟩
 · simpa only [List.length_map] using size
 · simp only [NKK_QueryStage.model6,NJU_Log.erase_bind,NKK_RawResult.source,run,NJU_Log.erase_pure]
   all_goals rfl

#print axioms eight
#print axioms six
end NKK_QueryDomain
