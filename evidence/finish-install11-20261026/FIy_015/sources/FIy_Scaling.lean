import FIy_ScaleReadback
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_Scaling
open Aeneas Aeneas.Std Result FIq_Native
open FIy_IteratorTraversal
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)

theorem total (range : Array QM 33#usize) (selector : QM)
    (hc : canonical range) (hs : Canon selector) :
    ∃ out, FIy_ScaleReadback.run range selector=ok out ∧
      canonical out ∧ decoded out=fun j=>decode selector*decoded range j := by
  let iter : IterMut := ⟨range.to_slice,0⟩
  obtain ⟨v,hv,final,back,hr,hsl,hi,hback⟩ :=
    FIy_IteratorCanonical.add_value_lanes_loop3_33 iter (fun x=>x) selector rfl
      (by exact range.property) hs (by
        intro j hj _
        exact hc _ (List.getElem_mem hj))
  let out : Array QM 33#usize :=
    ⟨range.val.mapIdx (fun i old=>(back final).slice.val[i]?.getD old),
      by simpa only [List.length_mapIdx] using range.property⟩
  have outVal : out.val=List.ofFn (fun i : Fin 33=>v i.val) := by
    change range.val.mapIdx (fun i old=>(back final).slice.val[i]?.getD old)=_
    rw [hback]
    exact FIy_ScaleReadback.readback range final v (by rw [hsl];exact range.property)
  refine ⟨out,?_,?_,?_⟩
  · unfold FIy_ScaleReadback.run
    simp only [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,bind_tc_ok]
    change (do let (im,b) ← Loop3 iter (fun x=>x) selector
               ok (⟨range.val.mapIdx (fun i old=>(b im).slice.val[i]?.getD old),_⟩ : Array QM 33#usize))=ok out
    rw [hr]
    rfl
  · intro x hx
    rw [outVal] at hx
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx
    subst x
    exact (hv j.val j.isLt).1
  · funext j
    change decode (out.val[j.val]'_)=_
    have he : out.val[j.val]'(by rw [out.property];exact j.isLt)=v j.val := by
      rw [outVal]
      simp only [List.getElem_ofFn]
    rw [he]
    exact (hv j.val j.isLt).2

theorem value (range out : Array QM 33#usize) (selector : QM)
    (hc : canonical range) (hs : Canon selector)
    (success : FIy_ScaleReadback.run range selector=ok out) :
    canonical out ∧ decoded out=fun j=>decode selector*decoded range j := by
  obtain ⟨out',hr,hcanon,hvalue⟩ := total range selector hc hs
  have he := Result.ok.inj (hr.symm.trans success)
  subst out'
  exact ⟨hcanon,hvalue⟩
#print axioms total
#print axioms value
end AspisR1.FIy_Scaling
end
