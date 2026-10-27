import XRz_FinishMaterialize
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishOwned
open XRx_FinishStep
def weights (w : Slice Q) : S8OwnedP6Finish.Weights :=
 ⟨w.val.map XRx_ValueOwned.oldQ,by simpa only [List.length_map] using w.property⟩
theorem roundtrip (q : S8OwnedP6ValueModel.Q) :
 XRx_ValueOwned.oldQ (XRz_FinishValue.newQ q)=q := rfl
/-- Complete Result equation for the SAME initial weight list and raw rows. -/
theorem source (b : verifier.BatchedWeights) (w : Slice Q) (len : w.length≤b.raw.length) :
 XRo_Join_Carriers.mapR (fun out : Slice Q => out.val.map XRx_ValueOwned.oldQ)
  (verifier.BatchedWeights.finish b w)=
 XRo_Join_Carriers.mapR (fun out : S8OwnedP6Finish.Weights => out.val)
  (S8OwnedP6.finish_owned b.raw (weights w)) := by
 have size : (weights w).length=w.length := by simp only [weights,alloc.vec.Vec.length,List.length_map]
 obtain ⟨out,run,hsize,cells⟩ := XRz_FinishMaterialize.source b w len
 obtain ⟨owned,hrun,hlen,hcells⟩ := S8OwnedP6Finish.finish_total_model b.raw (weights w) (by omega)
 change out.val.length=w.length at hsize
 change owned.val.length=(weights w).length at hlen
 rw [run,hrun]
 apply congrArg Result.ok
 apply List.ext_getElem?
 intro j
 by_cases hj : j<w.length
 · have hb : j<b.raw.val.length := by change j<b.raw.length; omega
   rw [List.getElem?_map,cells j hj,hcells j (by omega),List.getElem?_eq_getElem hb]
   simp only [Option.map_some,XRz_FinishMaterialize.rowValue,dif_pos (show j<b.raw.length by omega),roundtrip]
 · have ho : out.val[j]?=none := List.getElem?_eq_none (by omega)
   have hw : owned.val[j]?=none := List.getElem?_eq_none (by omega)
   rw [List.getElem?_map,ho,hw]
   rfl
#print axioms roundtrip
#print axioms source
end XRz_FinishOwned
