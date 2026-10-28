import NDO_JFy_PathLoop
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PathLiteral
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source (selector : field.QM31) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (hs : Canon selector) (hz : canonical o.z) (hb : canonical o.succ_z) :
    path_lanes_literal selector o ⦃ out => canonical out ⦄ := by
  have one := FIv_NativeValue.one.1
  have zero := JFy_ZeroArrays.source 17#usize
  unfold path_lanes_literal poseidon2.DIGEST_ELEMS
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JFy_PathLiteral
end
