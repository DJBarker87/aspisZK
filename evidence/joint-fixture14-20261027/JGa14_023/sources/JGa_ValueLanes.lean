import JGa_ValueSelectors
import JGa_ValueTail
import JGa_ValueScale
import JGa_ValueConservation
import JFy_ValueBits
import JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueLanes
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem bits0 (o : state_only_poseidon.StateOnlyPoseidonOpenings) (r : Array field.QM31 33#usize)
    (hz : canonical o.z) (hr : canonical r) :
    add_value_lanes_loop0 o r 0#usize ⦃ out => out.1=o ∧ canonical out.2 ⦄ := by
  obtain ⟨out,ho,hc⟩ := JFy_ValueBits0.source 10 0#usize o r rfl hz hr
  rw [ho]
  exact ⟨rfl,hc⟩
#print axioms bits0
@[step] theorem bits1 (o : state_only_poseidon.StateOnlyPoseidonOpenings) (r : Array field.QM31 33#usize)
    (hz : canonical o.succ_z) (hr : canonical r) :
    add_value_lanes_loop1 o r 0#usize ⦃ out => out.1=o ∧ canonical out.2 ⦄ := by
  obtain ⟨out,ho,hc⟩ := JFy_ValueBits1.source 10 0#usize o r rfl hz hr
  rw [ho]
  exact ⟨rfl,hc⟩
#print axioms bits1
@[step] theorem bits2 (o : state_only_poseidon.StateOnlyPoseidonOpenings) (r : Array field.QM31 33#usize)
    (hz : canonical o.xor12_z) (hr : canonical r) :
    add_value_lanes_loop2 o r 0#usize ⦃ out => out.1=o ∧ canonical out.2 ⦄ := by
  obtain ⟨out,ho,hc⟩ := JFy_ValueBits2.source 10 0#usize o r rfl hz hr
  rw [ho]
  exact ⟨rfl,hc⟩
#print axioms bits2

@[step] theorem source (packed : Array field.QM31 24#usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (hp : canonical packed)
    (hz : canonical o.z) (hb : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low) :
    add_value_lanes packed o s ⦃ out => canonical out ⦄ := by
  have zero := FIv_NativeValue.zero.1
  have zeros := JFy_ZeroArrays.source 33#usize
  have fact : add_value_lanes packed o s=(do
      let vs ← FIq_Native.core.array.Array.map FIy_ValueSelector.callback (Array.make 3#usize [0#usize,2#usize,4#usize]) s
      let q ← Array.index_usize vs 0#usize
      let q1 ← field.QM31.add field.QM31.ZERO q
      let q2 ← Array.index_usize vs 1#usize
      let q3 ← field.QM31.add q1 q2
      let q4 ← Array.index_usize vs 2#usize
      let selector ← field.QM31.add q3 q4
      let (o1,r1) ← add_value_lanes_loop0 o (Array.repeat 33#usize field.QM31.ZERO) 0#usize
      let (o2,r2) ← add_value_lanes_loop1 o1 r1 0#usize
      let (o3,r3) ← add_value_lanes_loop2 o2 r2 0#usize
      let r6 ← FIy_ValueTail.run o3 r3
      let r7 ← FIy_ScaleReadback.run r6 selector
      JGa_ValueConservation.run packed o3 s r7) := by
    unfold add_value_lanes FIy_ValueTail.run FIy_ScaleReadback.run JGa_ValueConservation.run
    simp only [bind_assoc_eq,bind_tc_ok]
    rfl
  rw [fact]
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_ValueLanes
end
