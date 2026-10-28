import NDO_JFy_Preweighted
import RPv_JFy_Steps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueConservation
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

def run (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (range : Array field.QM31 33#usize) :
    Result (Array field.QM31 24#usize) := do
  let packed1 ← add_preweighted packed 49#usize range
  let i2 ← 16#usize * VALUE_AUXILIARY_BLOCK
  let i3 ← i2 + 6#usize
  let conservation_selector ← pool_v1.pair_forest_copy_terminal.Selectors.row s i3
  let q15 ← Array.index_usize o.z 0#usize
  let q16 ← Array.index_usize o.z 1#usize
  let q17 ← field.QM31.sub q15 q16
  let q18 ← Array.index_usize o.z 2#usize
  let q19 ← field.QM31.sub q17 q18
  let q20 ← field.QM31.mul conservation_selector q19
  let q21 ← Array.index_usize o.succ_z 0#usize
  let q22 ← Array.index_usize o.succ_z 1#usize
  let q23 ← field.QM31.sub q21 q22
  let q24 ← field.QM31.mul conservation_selector q23
  add_preweighted packed1 82#usize (Array.make 2#usize [q20,q24])

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (range : Array field.QM31 33#usize)
    (hp : canonical packed) (hz : canonical o.z) (hb : canonical o.succ_z)
    (hh : canonical s.high) (hl : canonical s.low) (hr : canonical range) :
    run packed o s range ⦃ out => canonical out ⦄ := by
  unfold run VALUE_AUXILIARY_BLOCK
  step*
  all_goals first | assumption | scalar_tac | (intro x hx; simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl <;> assumption)
#print axioms source
end AspisR1.JGa_ValueConservation
end
