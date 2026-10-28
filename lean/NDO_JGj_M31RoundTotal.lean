import NDO_JGj_M31LoopTotal
import NDO_JGj_ExternalTotal
import NDO_JGj_ExternalPackedTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_M31RoundTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
theorem lazy (s : State) (a : Constants) (hs : canonical s) (ha : Bounded a) :
    ∃ out,state_only_poseidon.full_round_m31_constants s a=ok out ∧ canonical out := by
  obtain ⟨n,rn,cn⟩ := JGj_M31LoopTotal.source false 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s
    (by rw [poseidon2.POSEIDON2_WIDTH];decide) (by rw [poseidon2.POSEIDON2_WIDTH];rfl) ha hs
  obtain ⟨out,ro,co⟩ := JGj_ExternalTotal.source n cn
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.full_round_m31_constants
  change (do let n ← FJb_M31LoopStep.loop false ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s;state_only_poseidon.external_linear_lazy n)=ok out
  rw [rn,bind_tc_ok,ro]
theorem packed (s : State) (a : Constants) (hs : canonical s) (ha : Bounded a) :
    ∃ out,state_only_poseidon.full_round_m31_constants_packed s a=ok out ∧ canonical out := by
  obtain ⟨n,rn,cn⟩ := JGj_M31LoopTotal.source true 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s
    (by rw [poseidon2.POSEIDON2_WIDTH];decide) (by rw [poseidon2.POSEIDON2_WIDTH];rfl) ha hs
  obtain ⟨out,ro,co⟩ := JGj_ExternalPackedTotal.source n cn
  refine ⟨out,?_,co⟩
  unfold state_only_poseidon.full_round_m31_constants_packed
  change (do let n ← FJb_M31LoopStep.loop true ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ a s;state_only_poseidon.external_linear_packed n)=ok out
  rw [rn,bind_tc_ok,ro]
#print axioms lazy
#print axioms packed
end AspisR1.JGj_M31RoundTotal
end
