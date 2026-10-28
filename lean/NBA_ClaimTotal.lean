import NBA_ClaimCallee
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_ClaimTotal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

/-- Expansion, scratch powers and native claim are constructed from producers.
No y1, scratch, final parts or claim is selected by the caller of this theorem. -/
theorem construct (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
      {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ (y1 : Slice U8) (g : Array NE 29#usize) (out : NE),
      LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val ∧
      LPt_External.compact.expand_values compact before=ok (.Ok (),y1) ∧
      FIo_Native.weights.powers 29#usize gamma=ok g ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      NBA_Installed.actual.claim D sem y1 (NBA_ClaimCallee.wide inactive)
        (mapArray NBA_ClaimCallee.wide g) (NBA_ClaimCallee.wide kappa)=
        ok (.Ok (fromClaimE (LPq_Powers.claim out))) := by
  obtain ⟨y1,tr,_,_,expanded⟩ := LPt_LPs_ProducerTotal.expansion compact before len size
  obtain ⟨g,powers,_⟩ := LPq_Powers.source 29#usize gamma hc
  obtain ⟨out,trace,co,claim,_⟩ := NBA_ClaimCallee.source B D pub pre beforeSemantic
    challenges obs sem finish compact before y1 len size checked tr gamma inactive kappa hc hi hk g powers
  exact ⟨y1,g,out,tr,expanded,powers,trace,co,claim⟩

#print axioms construct
end AspisR1.NBA_ClaimTotal
end
