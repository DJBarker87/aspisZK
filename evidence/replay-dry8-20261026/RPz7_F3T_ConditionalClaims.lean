import RPz7_F3T_SourceCost
import RPz7_F3T_Conditional
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ConditionalClaims
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin F3T_Runtime
open RawExtractorCostComposedV2
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

/-- All per-attempt clauses, with source annotation cost. L157/L159 remain
explicit and the account sum is separately conditional, not a new headline. -/
theorem claims {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest) (runtime : Runtime)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime) :
    (∀ H : Bytes → State,(eval H (annotatedWith D (F3T_Installed.source c hashv)
        (F3T_Canon.canon (lift c P)))).2.2=true →
      mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
        (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) coins).2.total : Rat))≤
          ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat)) ∧
    (∀ run coins w,(ActualCostedExtractorM10.extractor.eval run coins).1=some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:Rat)^126+1/(2:Rat)^454≤1/(2:Rat)^120) ∧
    (F3T_RuntimeBound.failureModel runtime≤StartChargeNumeric.totalBound Q) ∧
    (Q≤OraclePortHeadlineFrozen2.Qmax → F3T_RuntimeBound.failureModel runtime≤(Q+1:Rat)*(1/(2:Rat)^100)) := by
  have bound := (F3T_Conditional.installed c D P Q queries hashv runtime raw binding).2
  exact ⟨F3T_SourceCost.accepted_attempt_cost c D P Q queries hashv raw,
    F3T_Cost.returned_relation,R1FinalSoundnessNumeric.extractor_abort_allowance,bound,
    fun range=>bound.trans (StartChargeNumeric.safe_range Q range)⟩

#print axioms claims
#print claims
end AspisR1.F3T_ConditionalClaims
end
