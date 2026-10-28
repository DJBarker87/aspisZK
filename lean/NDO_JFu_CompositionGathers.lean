import NDO_JFu_SelectedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CompositionGathers
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal
theorem callback0 (selected : Array field.QM31 84#usize) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) := by
  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected 0#usize i (by change 0<3;omega) (by omega)
  refine ⟨q,?_⟩
  unfold composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback0
theorem gather0 (selected : Array field.QM31 84#usize) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact callback0 selected
#print axioms gather0
theorem callback1 (selected : Array field.QM31 84#usize) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) := by
  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected 1#usize i (by change 1<3;omega) (by omega)
  refine ⟨q,?_⟩
  unfold composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback1
theorem gather1 (selected : Array field.QM31 84#usize) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact callback1 selected
#print axioms gather1
theorem callback2 (selected : Array field.QM31 84#usize) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) := by
  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected 2#usize i (by change 2<3;omega) (by omega)
  refine ⟨q,?_⟩
  unfold composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback2
theorem gather2 (selected : Array field.QM31 84#usize) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact callback2 selected
#print axioms gather2
theorem callback3 (selected : Array field.QM31 84#usize) (i : Usize) (bound : i.val<10) :
    ∃ q,composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) := by
  obtain ⟨col,add,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
  have boundCol : col.val<28 := by change col.val=16+i.val at value;omega
  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected 0#usize col (by change 0<3;omega) boundCol
  refine ⟨q,?_⟩
  unfold composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  rw [add,bind_tc_ok,read,bind_tc_ok]
#print axioms callback3
theorem gather3 (selected : Array field.QM31 84#usize) : ∃ out,
    array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact callback3 selected
#print axioms gather3
theorem source (selected : Array field.QM31 84#usize) : ∃ a b c m,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok a ∧
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok b ∧
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok c ∧
    array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok m := by
  obtain ⟨a,ha⟩ := gather0 selected
  obtain ⟨b,hb⟩ := gather1 selected
  obtain ⟨c,hc⟩ := gather2 selected
  obtain ⟨m,hm⟩ := gather3 selected
  exact ⟨a,b,c,m,ha,hb,hc,hm⟩
#print axioms source
end AspisR1.JFu_CompositionGathers
end
