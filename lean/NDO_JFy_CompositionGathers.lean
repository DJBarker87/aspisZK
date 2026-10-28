import NDO_JFy_SelectedRead
import NDO_JFy_BoundedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CompositionGathers
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal
theorem callback0 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) ∧ FIv_NativeValue.Canon q := by
  obtain ⟨q,read,hq⟩ := JFy_SelectedRead.source selected canonical 0#usize i (by change 0<3;omega) (by omega)
  refine ⟨q,?_,hq⟩
  unfold composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback0
theorem gather0 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out ∧ FIw_ArrayValue.canonical out := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  exact callback0 selected canonical
#print axioms gather0
theorem callback1 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) ∧ FIv_NativeValue.Canon q := by
  obtain ⟨q,read,hq⟩ := JFy_SelectedRead.source selected canonical 1#usize i (by change 1<3;omega) (by omega)
  refine ⟨q,?_,hq⟩
  unfold composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback1
theorem gather1 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out ∧ FIw_ArrayValue.canonical out := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  exact callback1 selected canonical
#print axioms gather1
theorem callback2 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) (i : Usize) (bound : i.val<16) :
    ∃ q,composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) ∧ FIv_NativeValue.Canon q := by
  obtain ⟨q,read,hq⟩ := JFy_SelectedRead.source selected canonical 2#usize i (by change 2<3;omega) (by omega)
  refine ⟨q,?_,hq⟩
  unfold composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  rw [read,bind_tc_ok]
#print axioms callback2
theorem gather2 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) : ∃ out,
    array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out ∧ FIw_ArrayValue.canonical out := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  exact callback2 selected canonical
#print axioms gather2
theorem callback3 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) (i : Usize) (bound : i.val<10) :
    ∃ q,composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut selected i=ok (q,selected) ∧ FIv_NativeValue.Canon q := by
  obtain ⟨col,add,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
  have boundCol : col.val<28 := by change col.val=16+i.val at value;omega
  obtain ⟨q,read,hq⟩ := JFy_SelectedRead.source selected canonical 0#usize col (by change 0<3;omega) boundCol
  refine ⟨q,?_,hq⟩
  unfold composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  rw [add,bind_tc_ok,read,bind_tc_ok]
#print axioms callback3
theorem gather3 (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) : ∃ out,
    array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok out ∧ FIw_ArrayValue.canonical out := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  exact callback3 selected canonical
#print axioms gather3
theorem source (selected : Array field.QM31 84#usize) (canonical : FIw_ArrayValue.canonical selected) : ∃ a b c m,
    (array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok a ∧ FIw_ArrayValue.canonical a) ∧
    (array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok b ∧ FIw_ArrayValue.canonical b) ∧
    (array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok c ∧ FIw_ArrayValue.canonical c) ∧
    (array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok m ∧ FIw_ArrayValue.canonical m) := by
  obtain ⟨a,ha⟩ := gather0 selected canonical
  obtain ⟨b,hb⟩ := gather1 selected canonical
  obtain ⟨c,hc⟩ := gather2 selected canonical
  obtain ⟨m,hm⟩ := gather3 selected canonical
  exact ⟨a,b,c,m,ha,hb,hc,hm⟩
#print axioms source
end AspisR1.JFy_CompositionGathers
end
