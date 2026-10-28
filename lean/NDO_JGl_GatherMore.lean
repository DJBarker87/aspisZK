import NDO_JGl_GatherValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_GatherMore
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (cells canonical)
open pool_v1.pair_forest_semantic_terminal
open JGl_GatherValue
theorem one (a : JGl_SelectedCells.Selected) (out : State) (ha : canonical a)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f1 field.QM31.ZERO a=ok out)
    (i : Fin (16#usize).val) : cells out i=cells a ⟨28+i.val,by have h:=i.isLt;change i.val<16 at h;change 28+i.val<84;omega⟩ := by
  let u : Usize := Usize.ofNatCore i.val (lt_trans i.isLt (16#usize).hBounds)
  have hi : u.val<16 := i.isLt
  have h := FJb_BuilderSelected.value 16#usize field.QM31.Insts.CoreMarkerCopy f1 field.QM31.ZERO a
    (by intro j hj; obtain ⟨q,hq,_⟩ := JFy_CompositionGathers.callback1 a ha j hj;exact ⟨q,hq⟩) out run u hi
  have r := selected a 1#usize u (by decide) hi
  change (do let q←selected_claim a 1#usize u;ok (q,a))=ok (cells out i,a) at h
  rw [r,bind_tc_ok] at h
  have hu : u.val=i.val := by scalar_tac
  have result := (Prod.mk.inj (Result.ok.inj h)).1.symm
  simpa only [show (1#usize).val=1 from rfl,show 1*28=28 from rfl,hu] using result
#print axioms one
theorem two (a : JGl_SelectedCells.Selected) (out : State) (ha : canonical a)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f2 field.QM31.ZERO a=ok out)
    (i : Fin (16#usize).val) : cells out i=cells a ⟨56+i.val,by have h:=i.isLt;change i.val<16 at h;change 56+i.val<84;omega⟩ := by
  let u : Usize := Usize.ofNatCore i.val (lt_trans i.isLt (16#usize).hBounds)
  have hi : u.val<16 := i.isLt
  have h := FJb_BuilderSelected.value 16#usize field.QM31.Insts.CoreMarkerCopy f2 field.QM31.ZERO a
    (by intro j hj; obtain ⟨q,hq,_⟩ := JFy_CompositionGathers.callback2 a ha j hj;exact ⟨q,hq⟩) out run u hi
  have r := selected a 2#usize u (by decide) hi
  change (do let q←selected_claim a 2#usize u;ok (q,a))=ok (cells out i,a) at h
  rw [r,bind_tc_ok] at h
  have hu : u.val=i.val := by scalar_tac
  have result := (Prod.mk.inj (Result.ok.inj h)).1.symm
  simpa only [show (2#usize).val=2 from rfl,show 2*28=56 from rfl,hu] using result
#print axioms two
end AspisR1.JGl_GatherMore
end
