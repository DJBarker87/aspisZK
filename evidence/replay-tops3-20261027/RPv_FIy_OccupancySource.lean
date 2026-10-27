import RPv_FIy_OccupancyPrefix
import RPv_FIy_OccupancyTail
set_option autoImplicit false
namespace AspisR1.FIy_OccupancySource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)

theorem factor (input output : NQ) (expected : U32) (opened : Array NQ 16#usize) :
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal input output expected opened=(do
      let (occupied,oneMinus,both,initial) ← FIy_OccupancyPrefix.run input output opened
      let middle ← pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
        ⟨0#usize,poseidon2.DIGEST_ELEMS⟩ opened oneMinus initial both
      FIy_OccupancyTail.run input output expected opened occupied oneMinus middle) := by
  unfold pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
    FIy_OccupancyPrefix.run FIy_OccupancyTail.run
  simp only [bind_assoc_eq]
  rfl
#print axioms factor
end AspisR1.FIy_OccupancySource
