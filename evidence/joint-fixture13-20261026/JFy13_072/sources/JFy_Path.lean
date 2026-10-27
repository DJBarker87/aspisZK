import JFy_PathLiteral
import JFy_Preweighted
import FIx_HighSum
import FIx_PathPacked
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Path
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem high (s : pool_v1.pair_forest_copy_terminal.Selectors) (ranges : Slice (core.ops.range.Range Usize))
    (hb : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64) (hs : canonical s.high) :
    sum_high s ranges ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hout,_⟩ := FIx_HighSum.source s ranges hb hs
  rw [call]
  exact hout
#print axioms high

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hb : canonical o.succ_z)
    (hh : canonical s.high) (hl : canonical s.low) :
    add_path_lanes packed o s ⦃ out => canonical out ⦄ := by
  unfold add_path_lanes
  step* <;> first | assumption | exact FIx_PathPacked.range_bounds | scalar_tac
#print axioms source
end AspisR1.JFy_Path
end
