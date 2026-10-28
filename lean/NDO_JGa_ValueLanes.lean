import NDO_JGa_ValueFinish
import NDO_JGa_ValueBitsSpecs
import NDO_JGa_ValueSelectors
import NDO_JGa_ValueTail
import NDO_JGa_ValueScale
import NDO_JGa_ValueConservation
import NDO_JFy_ValueBits
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueLanes
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : canonical packed)
    (hz : canonical o.z) (hb : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low) :
    add_value_lanes packed o s ⦃ out => canonical out ⦄ := by
  have zero := FIv_NativeValue.zero.1
  have zeros := JFy_ZeroArrays.source 33#usize
  unfold add_value_lanes
  step*
  all_goals change JGa_ValueFinish.run packed _ s _ _ ⦃ out => canonical out ⦄
  all_goals apply JGa_ValueFinish.source <;> first | assumption | (subst_vars; assumption)
#print axioms source
end AspisR1.JGa_ValueLanes
end
