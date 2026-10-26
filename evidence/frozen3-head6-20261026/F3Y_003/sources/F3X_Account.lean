import F3X_Preparation
import F3X_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_Account
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Complete installed source first, including rejected prefixes. The second
preparation pass exposes a same-run query map; its reads are already cached
on acceptance. No accepted execution or oracle is selected in this definition. -/
def submitted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) :
    Program Bytes State F3X_Projection.Output :=
  bind (F3T_Installed.source c hashv (input c s)) fun accepted =>
    if accepted then bind (F3X_Preparation.program c s) fun p=>.done (s,p)
    else .done (s,none)

def program {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (P : ByteProver) :=
  bind P (submitted c hashv)

def prior {A : Type} (account : Program Bytes State A) : Program Bytes State Unit :=
  bind account fun _=>.done ()

theorem prior_log {A : Type} (account : Program Bytes State A) (H : Bytes → State) :
    (eval H (prior account)).1=(eval H account).1 := by
  simp only [prior,eval_bind,eval,List.append_nil]

theorem accepted {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (success : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    eval H (submitted c hashv s)=
      ((eval H (F3T_Installed.source c hashv (input c s))).1 ++
        (eval H (F3X_Preparation.program c s)).1,(s,some e.run.p)) := by
  simp only [submitted,eval_bind,success,ite_true,F3X_Preparation.on_evidence c B s H e,
    eval,List.append_nil]

theorem output {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (P : ByteProver) (H : Bytes → State) :
    eval H (program c hashv P)=
      ((eval H P).1 ++ (eval H (submitted c hashv (eval H P).2)).1,
        (eval H (submitted c hashv (eval H P).2)).2) := by
  rw [program,eval_bind]

#print axioms prior_log
#print axioms accepted
#print axioms output
end AspisR1.F3X_Account
end
