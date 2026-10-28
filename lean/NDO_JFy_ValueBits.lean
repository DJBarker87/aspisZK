import NDO_JFy_ValueBits2
import RPv_FIx_ValueBitPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_ValueBits
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings) (range : Array field.QM31 33#usize)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z) (hr : canonical range) :
    ∃ out,FIx_ValueBitPrefix.calls o range=ok (o,out) ∧ canonical out ∧
      decoded out=FIx_ValueBitPrefix.model o (decoded range) := by
  obtain ⟨r1,h1,hc1⟩ := JFy_ValueBits0.source 10 0#usize o range rfl hz hr
  obtain ⟨r2,h2,hc2⟩ := JFy_ValueBits1.source 10 0#usize o r1 rfl hs hc1
  obtain ⟨r3,h3,hc3⟩ := JFy_ValueBits2.source 10 0#usize o r2 rfl hx hc2
  have call : FIx_ValueBitPrefix.calls o range=ok (o,r3) := by
    unfold FIx_ValueBitPrefix.calls
    rw [h1,bind_tc_ok]
    change (do let (o2,r2) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 o r1 0#usize
               pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 o2 r2 0#usize)=ok (o,r3)
    rw [h2,bind_tc_ok]
    exact h3
  exact ⟨r3,call,hc3,(FIx_ValueBitPrefix.value o o range r3 hz hs hx hr call).2.2⟩
#print axioms source
end AspisR1.JFy_ValueBits
end
