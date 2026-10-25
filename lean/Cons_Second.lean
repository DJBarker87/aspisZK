import Cons_NativeBuild
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Cons_Second
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation

theorem accepted {F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps
      (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish)
      (Uni_Install.current ops reserved query geo) B std) accounts1 accounts2 saved f s) :
    let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (ClaimsUnrolledSdk.sdkOps
      (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish)
      (Uni_Install.current ops reserved query geo) B std)
    ∃ t : Cons_Native.Witness,
      Cons_Native.Calls (AuS1_Install.base stage) finish reserved query geo D () s.pub s.proof s.checkpoint t ∧
      Cons_NativeBuild.Aux reserved query geo D () s.pub s.proof s.checkpoint t := by
  obtain ⟨t,calls,aux⟩ := Cons_NativeBuild.accepted (Op5T_Concrete.stage (AuS1_Install.base stage))
    finish reserved query geo _ () s.pub s.proof s.checkpoint cuts.second
  exact ⟨t,calls,aux⟩

#print axioms accepted
end AspisR1.Cons_Second
end
