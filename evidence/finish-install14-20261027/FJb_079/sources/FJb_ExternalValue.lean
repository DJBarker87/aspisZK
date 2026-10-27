import FJb_ColumnMeaning
import FJb_GroupedFold
import FJb_MatrixLoop
import FJb_TailLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ExternalValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_MatrixModel (Values)
def model (v : Values) (j : Fin (16#usize).val) : K :=
  let grouped :=  FJb_GroupedValues.grouped v
  grouped j+FJb_ColumnMeaning.sum grouped (j.val%4)
/-- Complete native external-linear VALUE on the original successful call,
including its actual first traversal,16 scalar sum cells,and final traversal. -/
theorem value (s out : State) (hs : canonical s)
    (run : state_only_poseidon.external_linear_lazy s=ok out) :
    canonical out ∧ decoded out=model (decoded s) := by
  unfold state_only_poseidon.external_linear_lazy at run
  obtain ⟨stage,hstage,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨sums,htable,run⟩ := FIv_Map.bind_success _ _ _ run
  have vs := FJb_MatrixLoop.value 4 0#usize s stage rfl hs hstage
  have stage_value : decoded stage=FJb_GroupedValues.grouped (decoded s) :=
    vs.2.trans (FJb_GroupedFold.full _)
  have bound := FJb_ColumnBound.value stage sums htable
  have vo := FJb_TailLoop.value 16 0#usize stage out sums rfl vs.1 bound run
  refine ⟨vo.1,?_⟩
  funext j
  have hv := vo.2 j
  have hz : (0#usize).val≤j.val := Nat.zero_le _
  rw [if_pos hz,FJb_ColumnMeaning.meaning stage sums htable j.val,stage_value] at hv
  exact hv
#print axioms value
end AspisR1.FJb_ExternalValue
end
