import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import ExtractedMaskReducer
import ExtractedMaskReducerOps

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalBoundSource

open AspisR1SelectedMaskProbe

abbrev P : Nat := 2147483647

/-- The checked source constant is the exact U64 value `7 * P`. This isolates
its one multiplication so the ignored Bool-bound traversal can consume it. -/
theorem external_local_limb_bound_success :
    ∃ bound : U64,
      state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND = .ok bound ∧
      bound.val = 7 * P := by
  let p64 : U64 := UScalar.cast .U64 field.P
  have hp64 : p64.val = P := by
    dsimp [p64, P]
    rw [AspisR1.ExtractedMaskReducerOps.cast_value]
    rw [field.P]
    norm_num
  have hproduct : (7#u64).val * p64.val < 2^64 := by
    rw [hp64]
    decide
  obtain ⟨bound, hmul, hv⟩ :=
    AspisR1.ExtractedMaskReducerOps.mul_success (7#u64) p64 hproduct
  refine ⟨bound, ?_, ?_⟩
  · unfold state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
    change (do
      let i ← lift (UScalar.cast .U64 field.P)
      UScalar.mul 7#u64 i) = .ok bound
    simp only [state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND,
      p64, lift, bind_tc_ok, hmul]
  · rw [hp64] at hv
    simpa only [P, show (7#u64).val = 7 by rfl] using hv

#print axioms external_local_limb_bound_success
end AspisR1.PoseidonExternalLocalBoundSource
