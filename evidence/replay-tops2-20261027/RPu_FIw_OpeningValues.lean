import RPu_FIw_BuilderValue
import RPu_FIw_SelectedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_OpeningValues
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
abbrev Claims := Array NQ 84#usize

theorem z (claims : Claims) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    out.val.map decode=(OraclePortStdBuilder.indices 16#usize).map
      (fun i=>FIv_NativeArray.value claims (0*28+i.val)) := by
  apply FIw_BuilderValue.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 decode
    (fun c i=>FIv_NativeArray.value c (0*28+i.val)) _ claims out run
  intro c i x c' called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIw_SelectedValue.value c 0#usize i q hq,rfl⟩
#print axioms z

theorem succ (claims : Claims) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    out.val.map decode=(OraclePortStdBuilder.indices 16#usize).map
      (fun i=>FIv_NativeArray.value claims (1*28+i.val)) := by
  apply FIw_BuilderValue.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 decode
    (fun c i=>FIv_NativeArray.value c (1*28+i.val)) _ claims out run
  intro c i x c' called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIw_SelectedValue.value c 1#usize i q hq,rfl⟩
#print axioms succ

theorem xor12 (claims : Claims) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    out.val.map decode=(OraclePortStdBuilder.indices 16#usize).map
      (fun i=>FIv_NativeArray.value claims (2*28+i.val)) := by
  apply FIw_BuilderValue.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 decode
    (fun c i=>FIv_NativeArray.value c (2*28+i.val)) _ claims out run
  intro c i x c' called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIw_SelectedValue.value c 2#usize i q hq,rfl⟩
#print axioms xor12
end AspisR1.FIw_OpeningValues
end
