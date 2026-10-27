import RPz8_F3X_Account
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Rejected
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

/-- No acceptance, parsing or opening-class restriction on the source prefix. -/
theorem submitted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (s : Submission) (H : Bytes → State)
    (rejected : (eval H (F3T_Installed.source c hashv (input c s))).2=false) :
    eval H (F3X_Account.submitted c hashv s) =
      ((eval H (F3T_Installed.source c hashv (input c s))).1,(s,none)) := by
  simp only [F3X_Account.submitted,eval_bind,rejected,Bool.false_eq_true,
    ite_false,eval,List.append_nil]

/-- Preprocessing and the exact attempted source log survive rejection,
including repeated reads. There is no preparation replay on this branch. -/
theorem adaptive {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (H : Bytes → State)
    (rejected : (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).2=false) :
    eval H (F3X_Account.program c hashv P) =
      ((eval H P).1 ++ (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).1,
        ((eval H P).2,none)) := by
  rw [F3X_Account.output,submitted c hashv _ H rejected]

#print axioms submitted
#print axioms adaptive
end AspisR1.RPx_Rejected
end
