import RPv_FIr_BuilderCanonical
import RPv_FIr_SelectedClaim
import RPu_FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_OpeningCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev Claims := Array NQ 84#usize

theorem z (claims : Claims) (out : Array NQ 16#usize)
    (all : ∀ x∈claims.val,Canon x)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) : ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (fun c=>∀ x∈c.val,Canon x) Canon _ claims out all run
  intro c i x c' initial called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIr_SelectedClaim.canonical c _ i q initial hq,initial⟩
#print axioms z

theorem succ (claims : Claims) (out : Array NQ 16#usize)
    (all : ∀ x∈claims.val,Canon x)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) : ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (fun c=>∀ x∈c.val,Canon x) Canon _ claims out all run
  intro c i x c' initial called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIr_SelectedClaim.canonical c _ i q initial hq,initial⟩
#print axioms succ

theorem xor12 (claims : Claims) (out : Array NQ 16#usize)
    (all : ∀ x∈claims.val,Canon x)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) : ∀ x∈out.val,Canon x := by
  apply FIr_BuilderCanonical.fromFn 16#usize pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    (fun c=>∀ x∈c.val,Canon x) Canon _ claims out all run
  intro c i x c' initial called
  unfold pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at called
  obtain ⟨q,hq,r1⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r1)
  exact ⟨FIr_SelectedClaim.canonical c _ i q initial hq,initial⟩
#print axioms xor12
end AspisR1.FIw_OpeningCanonical
end
