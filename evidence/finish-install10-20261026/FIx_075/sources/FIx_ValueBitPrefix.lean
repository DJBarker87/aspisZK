import FIx_ValueBits0
import FIx_ValueBits1
import FIx_ValueBits2
import FIx_ValueBitClosed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueBitPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

def calls (o : Openings) (range : Array NQ 33#usize) : Result (Openings × Array NQ 33#usize) := do
  let (o1,r1) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 o range 0#usize
  let (o2,r2) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 o1 r1 0#usize
  pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 o2 r2 0#usize

def model (o : Openings) (old : Fin (33#usize).val → K) : Fin (33#usize).val → K :=
  fun j=>if j.val<10 then FIx_ValueBitModel.bit o.z j.val
    else if j.val<20 then FIx_ValueBitModel.bit o.succ_z (j.val-10)
    else if j.val<30 then FIx_ValueBitModel.bit o.xor12_z (j.val-20) else old j

theorem value (o returned : Openings) (range out : Array NQ 33#usize)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hr : canonical range) (success : calls o range=ok (returned,out)) :
    returned=o ∧ canonical out ∧ decoded out=model o (decoded range) := by
  unfold calls at success
  obtain ⟨⟨o1,r1⟩,h1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨⟨o2,r2⟩,h2,success⟩ := FIv_Map.bind_success _ _ _ success
  have v1 := FIx_ValueBits0.value 10 0#usize o o1 range r1 (by rfl) hz hr h1
  have same1 := v1.1
  subst o1
  have v2 := FIx_ValueBits1.value 10 0#usize o o2 r1 r2 (by rfl) hs v1.2.1 h2
  have same2 := v2.1
  subst o2
  have v3 := FIx_ValueBits2.value 10 0#usize o returned r2 out (by rfl) hx v2.2.1 success
  refine ⟨v3.1,v3.2.1,?_⟩
  rw [v3.2.2,v2.2.2,v1.2.2]
  funext j
  rw [FIx_ValueBitClosed.value,FIx_ValueBitClosed.value,FIx_ValueBitClosed.value]
  have zeroVal : (0#usize).val=0 := rfl
  simp only [zeroVal,Nat.sub_zero]
  unfold model
  by_cases h10 : j.val<10
  · rw [if_pos h10,if_neg (show ¬(20+0≤j.val ∧ j.val<20+0+10) by omega),
      if_neg (show ¬(10+0≤j.val ∧ j.val<10+0+10) by omega),
      if_pos (show 0+0≤j.val ∧ j.val<0+0+10 by omega)]
  · rw [if_neg h10]
    by_cases h20 : j.val<20
    · rw [if_pos h20,if_neg (show ¬(20+0≤j.val ∧ j.val<20+0+10) by omega),
        if_pos (show 10+0≤j.val ∧ j.val<10+0+10 by omega)]
    · rw [if_neg h20]
      by_cases h30 : j.val<30
      · rw [if_pos h30,if_pos (show 20+0≤j.val ∧ j.val<20+0+10 by omega)]
      · rw [if_neg h30,if_neg (show ¬(20+0≤j.val ∧ j.val<20+0+10) by omega),
          if_neg (show ¬(10+0≤j.val ∧ j.val<10+0+10) by omega),
          if_neg (show ¬(0+0≤j.val ∧ j.val<0+0+10) by omega)]
#print axioms value
end AspisR1.FIx_ValueBitPrefix
end
