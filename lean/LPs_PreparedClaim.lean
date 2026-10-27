import LPs_NaturalDomain
import LPs_SemanticDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPs_PreparedClaim
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

/-- Conditional consumer join. Semantic and powers canonicality are derived.
Natural byte predicates remain explicit because the producer cannot co-import
with LPq; this is NOT a native prepared_claim closure theorem. -/
theorem native_result (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (compact y1 : Slice U8) (len : y1.val.length=928)
    (expanded : LPq_ExpandedWords.Expanded compact.val y1.val)
    (checked : LPq_ExpandedWords.CompactCanonical compact.val)
    (gamma inactive kappa : NE) (hc : canonE gamma) (hi : canonE inactive) (hk : canonE kappa)
    (g : Array NE 29#usize) (powers : FIo_Native.weights.powers 29#usize gamma=ok g) :
    ∃ out, LPq_PreparedTrace.Trace (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa out ∧ canonE out ∧
      LPq_PreparedClaim.program (toClaimSem sem) y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        inactive kappa=fun _ => ok (.Ok (LPq_Powers.claim out)) := by
  exact LPq_SelectedDomain.native_result (toClaimSem sem)
    (LPs_SemanticDomain.source B D pub pre beforeSemantic challenges obs sem finish)
    y1 (LPs_NaturalDomain.selected compact y1 len expanded checked)
    (XRo_Join_Carriers.arr LPq_Powers.claim g)
    (LPq_CarrierFacts.weights_from_powers gamma hc g powers) inactive kappa hi hk

#print axioms native_result
#print axioms LPq_CarrierFacts.native_unique
end AspisR1.LPs_PreparedClaim
end
