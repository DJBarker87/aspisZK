import R1Z.RealR2_SeedGuard
import R1Z.RealR2_Context
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR2_Seed
open Aeneas Aeneas.Std Result AspisR1ProverStreams
open R1Z.ProverCommitStreamSource
attribute [local instance] Classical.propDecidable

/-- The two outstanding primitive guard premises of mask_seed are discharged.
This does not assert freshness, independence, or a native caller/run join. -/
theorem seed_total_frame (hash : Hash) (binding entropy : Bytes32)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    ∃ encoded : Array U8 81#usize,
      aspis_core.state_only_hiding.StateOnlyHidingContext.encode context = ok encoded ∧
      state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy =
        if entropy = Array.repeat 32#usize 0#u8 then
          ok (core.result.Result.Err state_only_hiding.StateOnlyMaskBuildError.ZeroPrivateEntropy)
        else (do let answer ← hash (seedSlices binding encoded entropy)
                 ok (core.result.Result.Ok answer)) := by
  obtain ⟨encoded, hc⟩ := RealR2_Context.encode_total context
  refine ⟨encoded, hc, ?_⟩
  by_cases hz : entropy = Array.repeat 32#usize 0#u8
  · simp only [hz, if_true]
    simp [state_only_hiding.derive_state_only_mask_seed_from_entropy_ref,
      RealR2_SeedGuard.array_eq]
  · rw [if_neg hz]
    apply ProverCommitStreamSource.mask_seed hash binding entropy context encoded
    · simpa only [RealR2_SeedGuard.array_eq, hz, decide_false]
    · exact hc

#print axioms seed_total_frame
end R1Z.RealR2_Seed
