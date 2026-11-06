import NFN_GeometryPart08
import NJU_CommonObserved
set_option autoImplicit false
noncomputable section
namespace NKE_GeometryDomain
open Aeneas Aeneas.Std Result AspisR1
/-- The fixed12-cell native returning window is established by this SAME
CLOSED child at the actual TX2 range10..22, never a caller assumption. -/
theorem returned (queries : Array U32 22#usize) (out : AspisR1Stage2.verifier.QueryGeometry)
 (entered : NJC_ClosedCalls.geometry queries 10#usize 22#usize=ok (.Ok out)) :
 out.start=10#usize ∧ out.inverses.val.length=12 ∧ out.line_z.val.length=12 := by
 unfold NJC_ClosedCalls.geometry at entered
 have success := (Port3_QueryInstall.success_iff _ _).mp entered
 obtain ⟨rows,lines,flat,prefixes,product,suffix,resized,inverse,groups,
  count,hflat,hlines,hstart,hline,hgroups,hp,hplen,hs,hresize,hreverse,
  hinverse,htrace,hcontent,hguard,hframes⟩ :=
  NFN_NFB_GeometryComposed.accepted_physical queries 10#usize 22#usize
   (Or.inr ⟨rfl,rfl⟩) (fun _=>none) out success
 have linesSize : lines.val.length=12 := by
  rw [hlines,List.length_map,count]
  rfl
 refine ⟨hstart,?_,?_⟩
 · rw [hcontent,List.length_map,List.length_range,linesSize]
 · rw [hline,linesSize]
#print axioms returned
end NKE_GeometryDomain
