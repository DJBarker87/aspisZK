import FIy_OccupancyModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyList
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

theorem value (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
    (out : Array NQ 12#usize) (hi : Canon input) (ho : Canon output)
    (he : expected.val<FIw_ScalarArithmetic.P) (ha : canonical opened)
    (success : pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal input output expected opened=ok out) :
    canonical out ∧ out.val.map decode=R0P.occupancyLanesLiteral
      (decode input) (decode output) (expected.val : K) (fun i=>FIv_NativeArray.value opened i.val) := by
  have source := FIy_OccupancyMeaning.value input output expected opened out hi ho he ha success
  refine ⟨source.1,?_⟩
  have h : out.val.map decode=List.ofFn (decoded out) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_ofFn,out.property]
    · intro j hj _
      rw [List.getElem_map,List.getElem_ofFn]
      rfl
  rw [h,source.2,FIy_OccupancyModel.value]
#print axioms value
end AspisR1.FIy_OccupancyList
end
