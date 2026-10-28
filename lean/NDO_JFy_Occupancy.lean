import NDO_JFy_OccupancyLiteral
import NDO_JFy_Preweighted
import RPv_JFy_Steps
import NDO_JFy_PublicCanonical
import RPv_FIy_OccupancyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Occupancy
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
    add_occupancy_lanes packed p o s ⦃ out => canonical out ⦄ := by
  have zero := FIv_NativeValue.zero.1
  have one := FIv_NativeValue.one.1
  have v : p.variant=.PrivateTransfer := rfl
  unfold add_occupancy_lanes
  rw [FIy_OccupancyRows.input,bind_tc_ok,FIy_OccupancyRows.output]
  simp only [v,variant_expected_output,bind_tc_ok]
  step*
  all_goals first | assumption | scalar_tac
  all_goals intro x hx
  all_goals simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
  all_goals rcases hx with rfl|rfl <;> assumption
#print axioms source
end AspisR1.JFy_Occupancy
end
