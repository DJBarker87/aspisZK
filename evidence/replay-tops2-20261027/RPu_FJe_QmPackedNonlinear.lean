import RPu_FJb_QmLazyRound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_QmPackedNonlinear
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
/-- The complete nonlinear input to the actual final packed call, derived on
that same successful round. No nonlinear value is an input hypothesis. -/
theorem value (s : State) (constants : State) (out : Array NQ 4#usize)
    (hs : canonical s) (hc : canonical constants)
    (run : state_only_poseidon.full_round_packed s constants=ok out) :
    ∃ nonlinear : State,canonical nonlinear ∧
      decoded nonlinear=(fun j=>R0P.poseidonPow5 (decoded s j+decoded constants j)) ∧
      state_only_poseidon.external_linear_packed nonlinear=ok out := by
  unfold state_only_poseidon.full_round_packed at run
  obtain ⟨nonlinear,hn,tail⟩ := FIv_Map.bind_success _ _ _ run
  have vn := FJb_QmRoundLoop.value true 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ constants s nonlinear
    (by rw [poseidon2.POSEIDON2_WIDTH];decide)
    (by rw [poseidon2.POSEIDON2_WIDTH];rfl) hc hs hn
  refine ⟨nonlinear,vn.1,?_,tail⟩
  funext j
  have hv := vn.2 j
  have cond : (0#usize).val ≤ j.val ∧ j.val < poseidon2.POSEIDON2_WIDTH.val := by
    constructor
    · exact Nat.zero_le _
    · rw [poseidon2.POSEIDON2_WIDTH]
      exact j.isLt
  rw [if_pos cond] at hv
  exact hv.trans (by unfold R0P.poseidonPow5;ring)
#print axioms value
end AspisR1.FJe_QmPackedNonlinear
end
