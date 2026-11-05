import NFW_ScalarRho
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PreparedProducer
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NFW_PreparedPort

theorem cell (x : NE) : e (NFW_PowersCohort.toPublic x)=FIo_Install.fromE x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rfl

theorem array (g : Array NE 29#usize) :
 map e (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g)=FIp_DotsAdapter.fromArray g := by
 apply Subtype.ext
 simp [map,NFW_PowersCohort.mapArray,FIp_DotsAdapter.fromArray,Function.comp_def,cell]

/-- The SAME successful adopted producer determines both its gamma and its
entire scratch output. No independent powers result or canonical output is
assumed as a root premise. Native Prepared association remains a separate OPEN
obligation; this theorem supplies its concrete consumer-domain composition. -/
theorem scratch {H : Type}
 (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
 (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
 (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
 (v : AspisR1PublicPreparation.verifier.View) (hash : H)
 (out : AspisR1PublicPreparation.verifier.Prepared) (scratch old : Array PE 29#usize)
 (run : AspisR1PublicPreparation.PreparedScratchModel.prepare
  (AspisR1ClaimPreparedBridge.concreteBoundaries
   (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)) D sem v hash old=ok (.Ok out,scratch)) :
 ∃ g, FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative out.gamma)=ok g ∧
  scratch=NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g ∧
  map e scratch=FIp_DotsAdapter.fromArray g ∧
  NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (map e scratch)) := by
 have canonical := NFW_SampledDomains.prepared_gamma sampling D sem v hash out scratch old run
 have model := (NFW_PreparedCalls.calls _ D sem v hash out scratch old run).1
 change AspisR1ClaimPreparedBridge.powersPublic 29#usize out.gamma=ok scratch at model
 obtain ⟨g,native,source,holds⟩ := NFW_PowersCohort.source 29#usize
  (NFW_SampledDomains.toNative out.gamma) canonical
 rw [NFW_SampledDomains.roundtrip] at source
 have same := Result.ok.inj (model.symm.trans source)
 refine ⟨g,native,same,?_,?_⟩
 · rw [same];exact array g
 · rw [same,array]
   exact NFW_PowersDomain.query_domain _ canonical g native
#print axioms cell
#print axioms array
#print axioms scratch
end AspisR1.NFW_PreparedProducer
