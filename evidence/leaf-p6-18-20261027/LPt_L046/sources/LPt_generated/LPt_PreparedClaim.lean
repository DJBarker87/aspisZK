import LPt_ByteDomain
import LPt_LPs_ProducerTotal
import LPs_SemanticDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPt_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

/-- Same-carrier prepared_claim join. The natural compact/expanded predicates,
semantic canonicality and powers canonicality are all derived from producers. -/
theorem native_result (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before y1 : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (trace : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ out, LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      LPq_PreparedClaim.program (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (LPq_Powers.claim out)) := by
  obtain ⟨length,expanded,canonical⟩ :=
    LPt_ByteDomain.natural compact before y1 len size checked trace
  exact LPs_PreparedClaim.native_result B D pub pre beforeSemantic challenges obs sem finish
    compact y1 length expanded canonical gamma inactive kappa hc hi hk g powers

/-- Construct the expansion/output on every caller-shaped initial buffer.
Neither the output bytes nor prepared result are supplied as hypotheses. -/
theorem construct (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact before : Slice U8) (len : compact.val.length=464)
    (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ y1 : Slice U8, LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val ∧
      LPt_External.compact.expand_values compact before=ok (.Ok (),y1) ∧
      ∃ out, LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      LPq_PreparedClaim.program (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (LPq_Powers.claim out)) := by
  obtain ⟨y1,trace,_,_,expanded⟩ := LPt_LPs_ProducerTotal.expansion compact before len size
  exact ⟨y1,trace,expanded,native_result B D pub pre beforeSemantic challenges obs sem finish
    compact before y1 len size checked trace gamma inactive kappa hc hi hk g powers⟩

#print axioms construct

#print axioms native_result
#print axioms LPq_CarrierFacts.native_unique
end AspisR1.LPt_PreparedClaim
end
