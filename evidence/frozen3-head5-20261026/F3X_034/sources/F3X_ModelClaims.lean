import F3T_Cost
import F3T_ByteCarrier
import F3X_Margin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_ModelClaims
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_Canon F3T_ByteCarrier
open RawExtractorCostComposedV2 (Coins)

def Claims {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat) : Prop :=
  (∀ H : Bytes → State,(eval H (projected D (canon (lift c P)))).2.2=true →
    mean (fun coins : Coins=>
      ((ActualCostedExtractorM10.extractor.eval (eval H (projected D (canon (lift c P)))) coins).2.total : Rat))≤
        ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat)) ∧
  (∀ run coins w,(ActualCostedExtractorM10.extractor.eval run coins).1=some w →
    LiteralProtocol.relation run.2.1.1 w) ∧
  (1/(2:Rat)^126+1/(2:Rat)^454≤1/(2:Rat)^120)

theorem claims {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) : Claims c D P Q := by
  have lifted : ∀ H : Bytes → State,(eval H (lift c P)).1.length≤Q := by
    intro H
    rw [lift_eval]
    exact queries H
  refine ⟨F3T_Cost.accepted_attempt_cost D (lift c P) Q lifted,F3T_Cost.returned_relation,?_⟩
  norm_num [BinPerQueryNumeric.power454]

#print axioms claims
end AspisR1.F3X_ModelClaims
end
