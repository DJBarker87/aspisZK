import F3U_TwoPass
import F3T_SourceCost
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SourceCost
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3U_CollisionJoin
open RawExtractorCostComposedV2
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

theorem cost_or_collision {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (bad : Exception) (join : Join c D (F3T_Installed.source c hashv) bad) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P)))).2.2=true) :
    mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
      (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) coins).2.total : Rat))≤
      ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat) ∨
      bad H (eval H P).2.publicBytes (eval H P).2.stored := by
  rcases F3U_TwoPass.annotated_or_collision c D _ (F3T_Installed.physical c hashv) bad join _
    (canon_lift_carried c P) H accepted with joined | collision
  · left
    rw [joined] at accepted ⊢
    rw [←projected_eval]
    have ha : (eval H (projected D (F3T_Canon.canon (lift c P)))).2.2=true := by
      rw [projected_eval];exact accepted
    apply F3T_Cost.accepted_attempt_cost D (lift c P) Q _ H ha
    intro H;rw [lift_eval];exact queries H
  · right
    simpa only [F3T_Canon.canon_eval,lift_eval,F3T_Canon.canonInput,input] using collision

#print axioms cost_or_collision
end AspisR1.F3U_SourceCost
end
