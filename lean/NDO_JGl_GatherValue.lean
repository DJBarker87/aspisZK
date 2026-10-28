import NDO_JGl_ConcreteSelected
import NDO_JFy_CompositionGathers
import RPv_FJb_BuilderSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_GatherValue
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (cells canonical)
open pool_v1.pair_forest_semantic_terminal
abbrev State := Array field.QM31 16#usize
abbrev f0 := composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
abbrev f1 := composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
abbrev f2 := composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

theorem selected (a : JGl_SelectedCells.Selected) (row : Usize) (i : Usize)
    (hr : row.val<3) (hi : i.val<16) :
    selected_claim a row i=
      ok (cells a ⟨row.val*28+i.val,by change row.val*28+i.val<84;omega⟩) := by
  have spec : selected_claim a row i ⦃
      out=>out=cells a ⟨row.val*28+i.val,by change row.val*28+i.val<84;omega⟩ ⦄ := by
    unfold selected_claim
    rw [JFu_SelectedClaim.stride,bind_tc_ok]
    step*
    all_goals first | scalar_tac | (simp_all [cells])
  obtain ⟨out,run,rfl⟩ := WP.spec_imp_exists spec
  exact run
#print axioms selected

theorem zero (a : JGl_SelectedCells.Selected) (out : State) (ha : canonical a)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy f0 field.QM31.ZERO a=ok out)
    (i : Fin (16#usize).val) : cells out i=cells a ⟨i.val,by have h:=i.isLt;change i.val<16 at h;change i.val<84;omega⟩ := by
  let u : Usize := Usize.ofNatCore i.val (lt_trans i.isLt (16#usize).hBounds)
  have hi : u.val<16 := i.isLt
  have h := FJb_BuilderSelected.value 16#usize field.QM31.Insts.CoreMarkerCopy f0 field.QM31.ZERO a
    (by intro j hj; obtain ⟨q,hq,_⟩ := JFy_CompositionGathers.callback0 a ha j hj;exact ⟨q,hq⟩) out run u hi
  have r := selected a 0#usize u (by decide) hi
  change (do let q←selected_claim a 0#usize u;ok (q,a))=ok (cells out i,a) at h
  rw [r,bind_tc_ok] at h
  have hu : u.val=i.val := by scalar_tac
  have result := (Prod.mk.inj (Result.ok.inj h)).1.symm
  simpa only [show (0#usize).val=0 from rfl,Nat.zero_mul,Nat.zero_add,hu] using result
#print axioms zero
end AspisR1.JGl_GatherValue
end
