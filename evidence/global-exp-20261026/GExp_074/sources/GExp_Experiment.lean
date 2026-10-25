import GExp_SecondBudget
import GExp_PairAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_Experiment
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

structure FirstInputs where
  semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  pub : Slice U8
  proof : Slice U8
  split : Usize

structure SecondInputs where
  pub : Slice U8
  proof : Slice U8
  checkpoint : Slice U8

abbrev FirstReply := Result (core.result.Result (alloc.vec.Vec U8) AspisR1CurrentCaller.verifier.Error)
abbrev SecondReply := Result (core.result.Result Unit VTop_Stages.verifier.Error)
abbrev Outcome := FirstInputs × FirstReply × Option (SecondInputs × SecondReply)

def first (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit) (input : FirstInputs) :=
  SdkC_Oracle.program (GExp_FirstCode.code ops B std hashv D input.semantic input.pub input.proof input.split)

def second (ops : VTop_Stages.Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (input : SecondInputs) :=
  SdkC_Oracle.program (GExp_SecondCode.code ops reserved hashv D input.pub input.proof input.checkpoint)

/-- Chosen before H, including arbitrary oracle preprocessing and the adaptive
second submission AFTER the actual saved checkpoint reply. All earlier
oracle interactions are charged in adversary/chooseSecond's query budgets. -/
def program (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State FirstInputs)
    (chooseSecond : FirstInputs → alloc.vec.Vec U8 → Program Bytes State SecondInputs) :
    Program Bytes State Outcome :=
  bind adversary fun input => bind (first current B std hashv D1 input) fun reply =>
    match reply with
    | .ok (.Ok saved) => bind (chooseSecond input saved) fun next =>
        bind (second stage reserved hashv D2 next) fun out => .done (input,reply,some (next,out))
    | _ => .done (input,reply,none)

#print program
end AspisR1.GExp_Experiment
end
