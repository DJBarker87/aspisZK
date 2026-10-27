import GExp_FixedPair
import GExp_CollisionBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_FixedPairBudget
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem budget {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (f : FirstCut) (s : SecondCut)
    (H : Bytes → State) :
    (eval H (GExp_FixedPair.program adapter ops stage finish reserved query geo B std hashv f s)).1.length ≤ 22585 := by
  exact GExp_GlobalBudget.budget _ _ _ _ _ _ _ _ _ _ 0 0
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 0) H

#print axioms budget
end AspisR1.GExp_FixedPairBudget
end
