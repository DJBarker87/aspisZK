import F3X_Account
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_AccountPrior
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier

def program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (s : Submission) :=
  bind prior fun _=>F3X_Account.submitted c hashv s

theorem evaluation {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (s : Submission) (H : Bytes → State) :
    eval H (program c hashv prior s)=
      ((eval H prior).1++(eval H (F3X_Account.submitted c hashv s)).1,
        (eval H (F3X_Account.submitted c hashv s)).2) := by
  rw [program,eval_bind]

theorem actual {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (P : ByteProver) (H : Bytes → State) :
    eval H (program c hashv (F3X_Account.prior P) (eval H P).2)=
      eval H (F3X_Account.program c hashv P) := by
  rw [evaluation,F3X_Account.prior_log,F3X_Account.output]

#print axioms evaluation
#print axioms actual
end AspisR1.F3X_AccountPrior
end
