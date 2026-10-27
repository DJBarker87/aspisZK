import F3T_InstalledRecovered
import F3T_Cost
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_SourceCost
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawExtractorCostComposedV2

theorem accepted_attempt_cost {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (H : Bytes → State)
    (accepted : (eval H (annotatedWith D (F3T_Installed.source c hashv)
      (F3T_Canon.canon (lift c P)))).2.2=true) :
    mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
      (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) coins).2.total : Rat))≤
      ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat) := by
  have joined := F3T_ByteTransport.annotated_eq c D _ (F3T_Installed.physical c hashv) raw _
    (F3T_Carried.canon_lift_carried c P) H accepted
  rw [joined,←projected_eval] at accepted ⊢
  apply F3T_Cost.accepted_attempt_cost D (lift c P) Q _ H accepted
  intro H;rw [lift_eval];exact queries H

#print axioms accepted_attempt_cost
end AspisR1.F3T_SourceCost
end
