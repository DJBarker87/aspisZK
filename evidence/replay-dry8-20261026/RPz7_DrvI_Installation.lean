import RPz7_CPhy_Physical
import RPz7_AuS1_Finish
import RPz7_DrvI_Counterexample
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvI_Installation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {F CoreError : Type}
    (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CoreError) (stageBase : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)

/-- Literal stage dictionary used by CPhy_Physical.accepted_pair_unified. -/
def stage : VTop_Stages.Ops :=
  Tx2I_Install.stage (Op5T_Concrete.stage
    (Tx2N_Execution.control stageBase reserved query geo)) finish

/-- Literal SDK dictionary in CPhy's extraction, cuts and caller facts. -/
def sdk : AdapterRw.Ops :=
  ClaimsUnrolledSdk.sdkOps
    (Tx2I_Install.install adapter
      (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved query geo)) finish)
    (Uni_Install.current ops reserved query geo) B std

/-- No compatibility premise: the batch theorem uses this exact dictionary. -/
theorem same_batch_dictionary :
    sdk adapter ops reserved query geo stageBase finish B std =
      Op5T_SamePair.dictionary adapter (Uni_Install.base ops reserved query geo)
        (Tx2N_Execution.control stageBase reserved query geo) finish B std := rfl

/-- Same nominal digest instance, with Unit hash, as CPhy's second stage. -/
def digest := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
  (sdk adapter ops reserved query geo stageBase finish B std)

theorem installed_split : (stage reserved query geo stageBase finish).op16 = ok 10#usize := rfl

/-- A concrete failure of compatibility with the actual installed dictionary,
using its own types. D188/P6 do not constrain the arbitrary Implementation. -/
theorem silent_not_installed (H : Bytes → State) :
    eval H (DrvI_Counterexample.silent VTop_Trace.Call.op16) ≠
      eval H (.done (VTop_Trace.invoke (stage reserved query geo stageBase finish)
        VTop_Trace.Call.op16)) := by
  intro equal
  have values := congrArg Prod.snd equal
  change (Result.div : Result Usize) = ok 10#usize at values
  cases values

/-- The counterexample is on a successfully returning installed library call;
it does not postulate acceptance of an impossible source run. -/
theorem installed_call_success (H : Bytes → State) :
    eval H (.done (VTop_Trace.invoke (stage reserved query geo stageBase finish)
      VTop_Trace.Call.op16)) = ([],ok 10#usize) := rfl

#print axioms same_batch_dictionary
#print axioms installed_split
#print axioms silent_not_installed
#print axioms installed_call_success
#print sdk
#print digest
#print AspisR1.CPhy_Physical.accepted_pair_unified
#print AspisR1.EndP_Headline.deployed_headline
end AspisR1.DrvI_Installation
end
