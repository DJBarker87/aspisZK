import NKU_State
import NKU_MixedFrame
import NKK_FieldSites
import NKK_QueryWindows
import NKK_SectionFrames
import NKK_AllocationWidth
set_option autoImplicit false
noncomputable section
namespace NKU_Offsets
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold
theorem gamma (bytes : Slice U8) (r last : Reader) (values : List Value)
 (backing : r.bytes=bytes) (size : bytes.val.length=1768) (cursor : r.at.val=176)
 (returned : (program NKK_FieldSites.gammaKinds r).result=ok (.Ok (values,last))) :
 last.bytes=bytes ∧ last.at.val=320 := by
 have bound : r.at.val+NKK_FieldDomain.span NKK_FieldSites.gammaKinds≤r.bytes.val.length := by
  change r.at.val+144≤r.bytes.val.length
  rw [backing,size,cursor]
  omega
 have fr:=NKU_MixedFrame.frame NKK_FieldSites.gammaKinds r last values bound returned
 refine ⟨fr.1.trans backing,?_⟩
 have advance:=fr.2
 change last.at.val=r.at.val+144 at advance
 omega
theorem z (bytes : Slice U8) (r last : Reader) (values : List Value)
 (backing : r.bytes=bytes) (size : bytes.val.length=1768) (cursor : r.at.val=568)
 (returned : (program NKK_FieldSites.zKinds r).result=ok (.Ok (values,last))) :
 last.bytes=bytes ∧ last.at.val=712 := by
 have bound : r.at.val+NKK_FieldDomain.span NKK_FieldSites.zKinds≤r.bytes.val.length := by
  change r.at.val+144≤r.bytes.val.length
  rw [backing,size,cursor]
  omega
 have fr:=NKU_MixedFrame.frame NKK_FieldSites.zKinds r last values bound returned
 refine ⟨fr.1.trans backing,?_⟩
 have advance:=fr.2
 change last.at.val=r.at.val+144 at advance
 omega
theorem semantic (bytes : Slice U8) (start finish : Usize) (values : Array NKU.K 10#usize)
 (size : bytes.val.length=1768) (cursor : start.val=408)
 (returned : NIL_FreshOps.semantic bytes start=ok (.Ok (values,finish))) : finish.val=568 := by
 have advance:=NKK_SectionFrames.semantic bytes start finish values (by rw [size,cursor];omega) returned
 omega
theorem weights (bytes : Slice U8) (start finish : Usize) (before after : alloc.vec.Vec NKU.K)
 (size : bytes.val.length=1768) (cursor : start.val=712) (width : before.val.length=64)
 (returned : NIL_FreshOps.weights bytes start before=ok (.Ok (after,finish))) :
 finish.val=1736 ∧ after.val.length=64 := by
 have fr:=NKK_SectionFrames.weights bytes start finish before after (by rw [size,cursor,width];omega) returned
 constructor <;> omega
#print axioms gamma
#print axioms z
#print axioms semantic
#print axioms weights
end NKU_Offsets
