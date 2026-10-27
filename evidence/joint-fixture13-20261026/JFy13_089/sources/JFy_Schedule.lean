import JFy_InitialVariant
import JFy_InitialBuilder
import JFy_AbsorptionBuilder
import JFy_Path
import JFy_Preweighted
import JFy_PublicCanonical
import FIx_ScheduleIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Schedule
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem parts (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
    semantic_initial_and_absorption p o s ⦃ out => canonical out.1 ∧ canonical out.2 ⦄ := by
  have zero := FIv_NativeValue.zero.1
  unfold semantic_initial_and_absorption poseidon2.RATE
  step*
  all_goals first | assumption | scalar_tac
#print axioms parts

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
    add_schedule_lanes packed p o s ⦃ out => canonical out ⦄ := by
  unfold add_schedule_lanes
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JFy_Schedule
end
