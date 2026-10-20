import ExtractedOpeningCalls
import ExtractedDigest32SamplerTransport

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.Post25RhoSampleCaller

open AspisR1PublicPreparation.PreparedReachability
open AspisR1PublicPreparation.SamplerTransport

/-- On the two-fold prepared path, successful preparation retains the exact
row-32 digest block and the successful current QM31 sampler result stored as rho.
The sampler's existing rank and canonicality facts are then inherited. -/
theorem prepare_success_rho_sample {H : Type}
    (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H)
    (out : verifier.Prepared)
    (hfolds : transport.Variant.folds v.variant = .ok 2#usize)
    (hprep : PreparedModel.prepare B D sem v hash = .ok (.Ok out)) :
    ∃ before : transcript.Transcript H,
      ∃ queries : Array U32 22#usize,
      ∃ afterQueries last : transcript.Transcript H,
        ∃ block : Array U8 32#usize,
          B.queries D before 31#u8 v.final_message = .ok (.Ok queries, afterQueries) ∧
          transcript.Transcript.block D afterQueries 32#u8
            (Array.to_slice (Std.Array.empty U8)) = .ok (block, last) ∧
          sampler.qm31_sample block = .ok out.rho ∧
          ExtractedQM31SamplerCarrier.CurrentCanonicalQM
            (ExtractedQM31SamplerCarrier.toCurrent (toOld out.rho)) ∧
          ExtractedQM31SamplerCorrect.coordinates (toOld out.rho) =
            SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block) := by
  have hr := PreparedReachability.prepare_success B D sem v hash out hprep
  rcases hr with ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,
    hseed,hgamma,hbytes,hkappa,halpha0,htail⟩
  cases htail with
  | single hf tail =>
      simp [hfolds] at hf
  | double hf root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 tail =>
      rcases tail with ⟨queries, afterQueries, last, rho, claim,
        hqueries, hrho, hclaim, hout⟩
      have houtRho : out.rho = rho := by
        have hp := congrArg (fun p : verifier.Prepared => p.rho) hout
        simpa [PreparedReachability.output] using hp
      obtain ⟨block,hblock,hsample⟩ :=
        AspisR1PublicPreparation.OpeningCalls.rho_success
          B D afterQueries last 32#u8 PreparedReachability.emptyPayload rho hrho
      have hsampleOut : sampler.qm31_sample block = .ok out.rho := by
        simpa [houtRho] using hsample
      obtain ⟨q0,hq0,hcanonical,hcoords⟩ := SamplerTransport.sample_total block
      have heq : out.rho = q0 := Result.ok.inj (hsampleOut.symm.trans hq0)
      have hcanonOut :
          ExtractedQM31SamplerCarrier.CurrentCanonicalQM
            (ExtractedQM31SamplerCarrier.toCurrent (toOld out.rho)) := by
        simpa [heq] using hcanonical
      have hcoordsOut :
          ExtractedQM31SamplerCorrect.coordinates (toOld out.rho) =
            SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block) := by
        simpa [heq] using hcoords
      refine ⟨afterAlpha, queries, afterQueries, last, block, ?_, ?_, hsampleOut, hcanonOut, hcoordsOut⟩
      · exact hqueries
      · exact hblock

#print axioms prepare_success_rho_sample

end AspisR1PublicPreparation.Post25RhoSampleCaller
