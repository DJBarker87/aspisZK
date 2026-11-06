import NKK_QueryDomain
set_option autoImplicit false
noncomputable section
namespace NKK_QueryWindows
open Aeneas Aeneas.Std Result NKK_NativeRaw

def run (r : Reader) : NJU_Log.Run NJU_ResumeObserved.Event (List U32 × Reader) := do
 let (a,r1) ← NKK_QueryStage.model8 r
 let (b,r2) ← NKK_QueryStage.model8 r1
 let (c,r3) ← NKK_QueryStage.model6 r2
 pure (a++b++c,r3)

/-- The two eight-read windows and last six-read window establish one SAME
Reader chain, actual1768 backing, final cursor408 and exactly22 words. -/
theorem domain (r : Reader) (length : r.bytes.val.length=1768) (cursor : r.at.val=320) :
 ∃ (qs : List U32) (last : Reader), qs.length=22 ∧
 (run r).result=ok (qs,last) ∧ last.bytes=r.bytes ∧ last.at.val=408 := by
 obtain ⟨a,r1,size1,one,frame1,advance1⟩:=NKK_QueryDomain.eight r ⟨0,by decide⟩ length (by simpa using cursor)
 obtain ⟨b,r2,size2,two,frame2,advance2⟩:=NKK_QueryDomain.eight r1 ⟨1,by decide⟩ (by rw [frame1,length]) (by simpa using advance1)
 obtain ⟨c,r3,size3,three,frame3,advance3⟩:=NKK_QueryDomain.six r2 (by rw [frame2,frame1,length]) (by simpa using advance2)
 refine ⟨a++b++c,r3,?_,?_,frame3.trans (frame2.trans frame1),advance3⟩
 · simp only [List.length_append,size1,size2,size3]
 · simp only [run,NJU_Log.erase_bind,NJU_Log.erase_pure]
   rw [one]
   change ((NKK_QueryStage.model8 r1).result >>= fun pair=>
    (NKK_QueryStage.model6 pair.2).result >>= fun out=>ok (a++pair.1++out.1,out.2))=_
   rw [two]
   change ((NKK_QueryStage.model6 r2).result >>= fun out=>ok (a++b++out.1,out.2))=_
   rw [three]
   all_goals rfl

#print axioms domain
end NKK_QueryWindows
