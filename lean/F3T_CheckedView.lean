import F3T_Checked
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_CheckedView
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_Canon

def checks (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State)
    (hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1161)
      (eval H (projected D (canon P))))
    (ha : (eval H (original D (canon P))).2.2=true) :
    LiteralAcceptanceTerminal.Checks (eval H (projected D (canon P))).2.1.1
      ((LiteralByteProtocol.protocol D).transcript H (eval H (projected D (canon P))).2.1.1
        (eval H (projected D (canon P))).2.1.2 33).rounds := by
  rw [projected_eval]
  exact F3T_Checked.checks D P Q hq H hc ha
#print axioms checks
end AspisR1.F3T_CheckedView
end
