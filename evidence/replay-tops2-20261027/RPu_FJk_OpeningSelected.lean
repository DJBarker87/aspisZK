import RPu_FIw_OpeningValues
import RPu_FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_OpeningSelected
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open FIw_ArrayValue (decoded)
/-- Ordered constructor indices retain their exact vector interpretation. -/
theorem indices {N : Usize} (out : Array NQ N) (f : Nat → K)
    (h : out.val.map decode=(OraclePortStdBuilder.indices N).map (fun i=>f i.val)) :
    decoded out=fun i=>f i.val := by
  apply FIx_ArrayMeaning.decoded_of_map
  refine h.trans ?_
  simp only [OraclePortStdBuilder.indices,List.map_ofFn,Function.comp_def]
  congr 1

theorem z (claims : Array NQ 84#usize) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    decoded out=fun i=>FIv_NativeArray.value claims i.val := by
  have h := indices out (fun i=>FIv_NativeArray.value claims (0*28+i)) (FIw_OpeningValues.z claims out run)
  simpa only [Nat.zero_mul,Nat.zero_add] using h

theorem succ (claims : Array NQ 84#usize) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    decoded out=fun i=>FIv_NativeArray.value claims (28+i.val) := by
  have h := indices out (fun i=>FIv_NativeArray.value claims (1*28+i)) (FIw_OpeningValues.succ claims out run)
  simpa only [Nat.one_mul] using h

theorem xor12 (claims : Array NQ 84#usize) (out : Array NQ 16#usize)
    (run : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO claims=ok out) :
    decoded out=fun i=>FIv_NativeArray.value claims (56+i.val) := by
  exact indices out (fun i=>FIv_NativeArray.value claims (2*28+i)) (FIw_OpeningValues.xor12 claims out run)
#print axioms indices
#print axioms z
#print axioms succ
#print axioms xor12
end AspisR1.FJk_OpeningSelected
end
