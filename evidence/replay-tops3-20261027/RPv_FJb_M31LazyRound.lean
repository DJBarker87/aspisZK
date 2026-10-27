import RPv_FJb_ExternalExact
import RPv_FJb_M31Loop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_M31LazyRound
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
open FIv_NativeValue (K)
open FJb_TailCell (cell)
/-- Complete native M31-constant full round, including the ORIGINAL nonlinear
traversal and external-linear body on their SAME intermediate state. -/
theorem value (s out : State) (constants : Constants) (hs : canonical s) (hc : Bounded constants)
    (run : state_only_poseidon.full_round_m31_constants s constants=ok out) :
    canonical out ∧ decoded out=R0P.poseidonFullRound (decoded s) (fun j=>((cell constants j).val : K)) := by
  unfold state_only_poseidon.full_round_m31_constants at run
  obtain ⟨nonlinear,hn,run⟩ := FIv_Map.bind_success _ _ _ run
  have vn := FJb_M31Loop.value false 16 ⟨0#usize,poseidon2.POSEIDON2_WIDTH⟩ constants s nonlinear
    (by rw [poseidon2.POSEIDON2_WIDTH];decide)
    (by rw [poseidon2.POSEIDON2_WIDTH];rfl) hc hs hn
  have he : decoded nonlinear=(fun j=>R0P.poseidonPow5 (decoded s j+((cell constants j).val : K))) := by
    funext j
    have hv := vn.2 j
    have cond : (0#usize).val ≤ j.val ∧ j.val < poseidon2.POSEIDON2_WIDTH.val := by
      constructor
      · exact Nat.zero_le _
      · rw [poseidon2.POSEIDON2_WIDTH]
        exact j.isLt
    rw [if_pos cond] at hv
    exact hv.trans (by unfold R0P.poseidonPow5;ring)
  have ve := FJb_ExternalExact.value nonlinear out vn.1 run
  exact ⟨ve.1,ve.2.trans (congrArg R0P.poseidonExternalLinear he)⟩
#print axioms value
end AspisR1.FJb_M31LazyRound
end
