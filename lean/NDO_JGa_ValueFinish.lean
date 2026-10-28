import NDO_JGa_ValueScale
import NDO_JGa_ValueConservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueFinish
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

def run (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (range6 : Array field.QM31 33#usize)
    (range_selector : field.QM31) : Result (Array field.QM31 24#usize) := do
  let (iter,into_iter_back) ← MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter range6
  let (im,back) ← add_value_lanes_loop3 iter (fun im=>im) range_selector
  let range := into_iter_back (back im)
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
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (r : Array field.QM31 33#usize)
    (sel : field.QM31) (hp : canonical packed) (hz : canonical o.z) (hb : canonical o.succ_z)
    (hh : canonical s.high) (hl : canonical s.low) (hr : canonical r) (hs : Canon sel) :
    run packed o s r sel ⦃ out => canonical out ⦄ := by
  have factor : run packed o s r sel=(do
      let scaled ← FIy_ScaleReadback.run r sel
      JGa_ValueConservation.run packed o s scaled) := by
    unfold run FIy_ScaleReadback.run JGa_ValueConservation.run
    simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
    congr 1
  rw [factor]
  step*
#print axioms source
end AspisR1.JGa_ValueFinish
end
