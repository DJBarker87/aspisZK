import FJb_LeadingLoop
import FJa_PoseidonOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_LeadingOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
/-- The absorption VALUE on the SAME leading call. The subsequent linear
and nonlinear rounds remain actual source calls, not output premises. -/
theorem value (o : Openings) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z)
    (run : state_only_poseidon.leading_pair_packed o=ok out) :
    ∃ (a initial middle : Array NQ 16#usize) (c0 c1 : Array U32 16#usize),
      state_only_poseidon.leading_pair_packed_loop
        ⟨0#usize,poseidon2.RATE⟩ o.xor12_z o.z=ok a ∧
      canonical a ∧
      (∀ j : Fin (16#usize).val,decoded a j=
        if j.val < 8 then decoded o.z j+decoded o.xor12_z j else decoded o.z j) ∧
      state_only_poseidon.external_linear_lazy a=ok initial ∧
      Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize=ok c0 ∧
      state_only_poseidon.full_round_m31_constants initial c0=ok middle ∧
      Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize=ok c1 ∧
      state_only_poseidon.full_round_m31_constants_packed middle c1=ok out := by
  unfold state_only_poseidon.leading_pair_packed at run
  obtain ⟨a,ha,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨initial,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨c0,hc0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨middle,hm,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨c1,hc1,run⟩ := FIv_Map.bind_success _ _ _ run
  have va := FJb_LeadingLoop.value 8 ⟨0#usize,poseidon2.RATE⟩ o.xor12_z o.z a
    (by rw [poseidon2.RATE];decide) (by rw [poseidon2.RATE];rfl) hx hz ha
  refine ⟨a,initial,middle,c0,c1,ha,va.1,?_,hi,hc0,hm,hc1,run⟩
  intro j
  simpa only [poseidon2.RATE,show (0#usize).val=0 from rfl,
    show (8#usize).val=8 from rfl,Nat.zero_le,true_and] using va.2 j
#print axioms value
end AspisR1.FJb_LeadingOnRun
end
