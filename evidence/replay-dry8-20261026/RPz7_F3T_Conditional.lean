import RPz7_F3T_RuntimeBound
import F3T_Cost
import RPz7_F3T_Combined
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Conditional
open Aeneas Aeneas.Std
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin F3T_Runtime
open RawExtractorCostComposedV2

/-- Candidate model/runtime endpoint with L157 and L159 visibly RETAINED.
This is not the requested deployed_candidate with L157 discharged. -/
theorem installed {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (runtime : Runtime)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime) :
    (∀ H : Bytes → State,(eval H (projected D (F3T_Canon.canon (lift c P)))).2.2=true →
      mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
        (eval H (projected D (F3T_Canon.canon (lift c P)))) coins).2.total : Rat))≤
        ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat)) ∧
    F3T_RuntimeBound.failureModel runtime≤StartChargeNumeric.totalBound Q := by
  have lifted : ∀ H : Bytes → State,(eval H (lift c P)).1.length≤Q := by
    intro H;rw [lift_eval];exact queries H
  exact ⟨F3T_Cost.accepted_attempt_cost D (lift c P) Q lifted,
    F3T_RuntimeBound.failure_bound c D _ (F3T_Installed.physical c hashv) raw P Q queries runtime binding⟩

#print axioms installed
end AspisR1.F3T_Conditional
end
