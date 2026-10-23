import R1Z.RealR2_Seed
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR2_SeedImage
open Aeneas Aeneas.Std Result WP AspisR1ProverStreams
open R1Z.ProverCommitStreamSource
attribute [local instance] Classical.propDecidable

/-- Concrete native seed function to the fixed-write context model, for every
entropy value, preserving the supplied hash's observable behaviour. -/
theorem seed_image (hash : Hash) (binding entropy : Bytes32)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    ∃ encoded : Array U8 81#usize, encoded.val = RealR2_Context.frame context ∧
      state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy =
        if entropy = Array.repeat 32#usize 0#u8 then
          ok (core.result.Result.Err state_only_hiding.StateOnlyMaskBuildError.ZeroPrivateEntropy)
        else (do let answer ← hash (seedSlices binding encoded entropy)
                 ok (core.result.Result.Ok answer)) := by
  obtain ⟨encoded, hc, hs⟩ := RealR2_Seed.seed_total_frame hash binding entropy context
  have hf := RealR2_Context.encode_frame context
  rw [hc] at hf
  exact ⟨encoded, by simpa only [spec_ok] using hf, hs⟩

#print axioms seed_image
end R1Z.RealR2_SeedImage
