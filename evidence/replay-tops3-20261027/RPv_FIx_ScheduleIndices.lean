import RPv_FIx_ScheduleModel
import RPu_FIw_WordValue
set_option autoImplicit false
namespace AspisR1.FIx_ScheduleIndices
open Aeneas Aeneas.Std Result FIq_Native

theorem rate_bound : poseidon2.RATE.val<(16#usize).val := by
  rw [poseidon2.RATE]
  scalar_tac

theorem rate_plus_one (i : Usize) (run : poseidon2.RATE+1#usize=ok i) : i.val=9 := by
  have v := FIw_WordValue.add poseidon2.RATE 1#usize i run
  rw [poseidon2.RATE] at v
  scalar_tac

theorem nine_bound (i : Usize) (value : i.val=9) : i.val<(16#usize).val := by
  rw [value]
  scalar_tac

theorem node_bounds : ∀ r∈FIx_ScheduleModel.nodeRanges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
  intro r hr
  simp only [FIx_ScheduleModel.nodeRanges,Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> constructor <;> scalar_tac
#print axioms rate_bound
#print axioms rate_plus_one
#print axioms nine_bound
#print axioms node_bounds
end AspisR1.FIx_ScheduleIndices
