import NGN_Opening
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_ScalarDomains
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFW_PreparedControl

/-- Establishes the powers input domain at the scalar cut itself, before a
whole prepare result is known. Native realization of this call remains OPEN. -/
theorem gamma {H : Type} (sampling : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
 (before after : transcript.Transcript H) (payload : Slice U8) (value : PE)
 (call : PreparedModel.scalar (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)
  D before 27#u8 payload true=ok (value,after)) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative value) := by
 apply NFW_SampledDomains.gamma_canonical
 exact AspisR1ClaimPreparedBridge.scalar_candidate_gamma_canonical
  (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary sampling) D before after 27#u8 payload value call

/-- Installs the CLOSED powers packet on the exact scalar returned at S1.
No successful whole constructor or independently chosen powers result occurs. -/
theorem gamma_powers {H : Type} (sampling : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
 (before after : transcript.Transcript H) (payload : Slice U8) (value : PE)
 (call : PreparedModel.scalar (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)
  D before 27#u8 payload true=ok (value,after)) :
 ∃ g, FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative value)=ok g ∧
  AspisR1ClaimPreparedBridge.powersPublic 29#usize value=ok (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) ∧
  (∀ x∈g.val,NFN_LPi_FieldValues.canonE x) := by
 have canon := gamma sampling D before after payload value call
 obtain ⟨g,hg,hp,hc⟩ := NFW_PowersCohort.source 29#usize (NFW_SampledDomains.toNative value) canon
 rw [NFW_SampledDomains.roundtrip] at hp
 exact ⟨g,hg,hp,hc⟩
#print axioms gamma
#print axioms gamma_powers
end AspisR1.NGN_ScalarDomains
