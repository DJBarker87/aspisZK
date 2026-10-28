import NDO_JFy_OccupancyLoop
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_OccupancyLiteral
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source (input output : field.QM31) (expected : U32) (a : Array field.QM31 16#usize)
    (hi : Canon input) (ho : Canon output) (he : expected.val<2147483647) (ha : canonical a) :
    occupancy_lanes_literal input output expected a ⦃ out => canonical out ⦄ := by
  have one := FIv_NativeValue.one.1
  have zero := JFy_ZeroArrays.source 12#usize
  unfold occupancy_lanes_literal poseidon2.DIGEST_ELEMS
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JFy_OccupancyLiteral
end
