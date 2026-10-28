import NDO_JGa_ValueSelectors
import NDO_JGa_ValueTail
import NDO_JGa_ValueScale
import NDO_JGa_ValueConservation
import NDO_JFy_ValueBits
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueBitsSpecs
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

end AspisR1.JGa_ValueBitsSpecs
end
