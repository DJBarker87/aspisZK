import S4ConcreteResumeTwelveFieldsRootV2
import S4ClaimPowersSemanticV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4ResumedPowersSemanticV1
open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S4FullTx2CandidateFieldsRootV1
open AspisR1S4ConcreteResumeTwelveFieldsRootV2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1FastDotsTailFieldProductRootV1

theorem same_resume_source_powers_exact {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H) (checkpoint proof public_bytes : Slice U8)
    (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hresume : verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops.resumeOps)
      inst checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)))
    (hpowers : sourceP6WeightsPowers 29#usize p.gamma = .ok g) :
    ∀ j : Fin 29,
      wideDecoded ((AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g).val[j.val]'(by scalar_tac)) =
        AspisR1CurrentPreparedClaim.Concrete.decode (stage2ToClaim p.gamma) ^ j.val := by
  have hraw := AspisR1S4ResumeGammaActualCanonicalV1.resume_gamma_canonical
    ops.resumeOps inst checkpoint proof public_bytes transport.Variant.S2 hash p a hresume
  have hc := raw_bounds_claim_canonical p.gamma hraw
  obtain ⟨powers,hpow,harray⟩ := source_powers_same_claim_array p.gamma g hc hpowers
  exact S4ClaimPowersSemanticV1.caller_powers_exact _ _ powers hc hpow harray
#print axioms same_resume_source_powers_exact
end AspisR1.S4ResumedPowersSemanticV1
