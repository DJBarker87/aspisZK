import RPv_FIy_ScaleReadback
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueScale
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIy_IteratorTraversal

@[step] theorem source (a : Array field.QM31 33#usize) (selector : field.QM31)
    (ha : canonical a) (hs : Canon selector) :
    FIy_ScaleReadback.run a selector ⦃ out => canonical out ⦄ := by
  let iter : IterMut := ⟨Array.to_slice a,0⟩
  obtain ⟨v,hv,im,back,call,hslice,hi,hback⟩ :=
    FIy_IteratorCanonical.add_value_lanes_loop3_33 iter id selector rfl (by exact a.property)
      hs (by intro j hj _;exact ha _ (List.getElem_mem hj))
  have hlen : im.slice.val.length=33 := by rw [hslice];exact a.property
  have readback := FIy_ScaleReadback.readback a im v hlen
  have spec : ∃ out,FIy_ScaleReadback.run a selector=ok out ∧ out.val=List.ofFn (fun i : Fin 33=>v i.val) := by
    unfold FIy_ScaleReadback.run
    change ∃ out,(do let (im,back) ← Loop3 iter id selector; ok (⟨a.val.mapIdx (fun i old=>(back im).slice.val[i]?.getD old),by simp [a.property]⟩ : Array field.QM31 33#usize))=ok out ∧ _
    rw [call,bind_tc_ok]
    refine ⟨_,rfl,?_⟩
    change a.val.mapIdx (fun i old=>(back im).slice.val[i]?.getD old)=_
    rw [hback]
    exact readback
  obtain ⟨out,ho,hout⟩ := spec
  rw [ho]
  intro x hx
  rw [hout,List.mem_ofFn] at hx
  obtain ⟨i,rfl⟩ := hx
  exact (hv i.val i.isLt).1
#print axioms source
end AspisR1.JGa_ValueScale
end
