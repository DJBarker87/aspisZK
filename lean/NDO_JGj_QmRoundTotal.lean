import NDO_JGj_QmLoopTotal
import NDO_JGj_ExternalTotal
import NDO_JGj_ExternalPackedTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_QmRoundTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem lazy (s : State) (a : State) (hs : canonical s) (ha : canonical a) :
    ∃ out,state_only_poseidon.full_round s a=ok out ∧ canonical out := by
  obtain ⟨n,rn,cn⟩ := JGj_QmLoopTotal.source false 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s
    (by rw [poseidon2.POSEIDON2_WIDTH];decide) (by rw [poseidon2.POSEIDON2_WIDTH];rfl) ha hs
  obtain ⟨out,ro,co⟩ := JGj_ExternalTotal.source n cn
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.full_round
  change (do let n ← FJb_QmRoundStep.loop false ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s;state_only_poseidon.external_linear_lazy n)=ok out
  rw [rn,bind_tc_ok,ro]
theorem packed (s : State) (a : State) (hs : canonical s) (ha : canonical a) :
    ∃ out,state_only_poseidon.full_round_packed s a=ok out ∧ canonical out := by
  obtain ⟨n,rn,cn⟩ := JGj_QmLoopTotal.source true 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s
    (by rw [poseidon2.POSEIDON2_WIDTH];decide) (by rw [poseidon2.POSEIDON2_WIDTH];rfl) ha hs
  obtain ⟨out,ro,co⟩ := JGj_ExternalPackedTotal.source n cn
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.full_round_packed
  change (do let n ← FJb_QmRoundStep.loop true ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s;state_only_poseidon.external_linear_packed n)=ok out
  rw [rn,bind_tc_ok,ro]
#print axioms lazy
#print axioms packed
end AspisR1.JGj_QmRoundTotal
end
