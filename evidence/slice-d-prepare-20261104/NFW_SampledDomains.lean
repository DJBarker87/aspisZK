import NFW_PreparedPort
import NFW_PowersCohort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_SampledDomains
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
open NFW_PreparedPort

def toNative (x : PE) : NE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem roundtrip (x : PE) : NFW_PowersCohort.toPublic (toNative x)=x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rfl

theorem gamma_canonical (x : PE)
 (h : AspisR1CurrentPreparedClaim.Concrete.Canonical (AspisR1ClaimPreparedBridge.toClaimE x)) :
 canonE (toNative x) := h

theorem rho (p : AspisR1PublicPreparation.verifier.Prepared) (block : Array U8 32#usize)
 (sample : AspisR1PublicPreparation.sampler.qm31_sample block=ok p.rho) :
 NBF_PowerStep.Canonical (prepared p).rho := by
 have old := AspisR1PublicPreparation.SamplerTransport.sample_toOld_success block p.rho sample
 have h := ExtractedQM31SamplerCorrect.sample_canonical_of_success block
  (AspisR1PublicPreparation.SamplerTransport.toOld p.rho) old
 apply rho_canonical p
 exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩

/-- Derives the powers domain from this same successful adopted producer.
This does not assume a canonical gamma as an independent caller premise. -/
theorem prepared_gamma {H : Type}
 (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
 (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
 (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
 (v : AspisR1PublicPreparation.verifier.View) (hash : H)
 (out : AspisR1PublicPreparation.verifier.Prepared) (scratch old : Array PE 29#usize)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare
  (AspisR1ClaimPreparedBridge.concreteBoundaries
   (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)) D sem v hash old=ok (.Ok out,scratch)) :
 canonE (toNative out.gamma) := by
 exact gamma_canonical out.gamma
  (AspisR1ClaimPreparedBridge.prepared_candidate_samplers_canonical sampling D sem v hash out scratch old run).1

/-- Both nominal ports copy the exact original gamma limbs. -/
theorem same_gamma (p : AspisR1PublicPreparation.verifier.Prepared) :
 FIo_Install.toE (prepared p).gamma=toNative p.gamma := rfl

theorem powers (x : PE)
 (h : AspisR1CurrentPreparedClaim.Concrete.Canonical (AspisR1ClaimPreparedBridge.toClaimE x)) :
 ∃ g, FIo_Native.weights.powers 29#usize (toNative x)=ok g ∧
  AspisR1ClaimPreparedBridge.powersPublic 29#usize x=ok (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) ∧
  (∀ z∈g.val,canonE z) := by
 simpa only [roundtrip] using NFW_PowersCohort.source 29#usize (toNative x) (gamma_canonical x h)
#print axioms roundtrip
#print axioms gamma_canonical
#print axioms rho
#print axioms prepared_gamma
#print axioms same_gamma
#print axioms powers
end AspisR1.NFW_SampledDomains
