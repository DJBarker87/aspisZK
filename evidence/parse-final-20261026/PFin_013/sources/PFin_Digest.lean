import AuS1_Install
import Tx1Q_SameCut
import Uni_Install
import Tx1Q_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_Digest
open Aeneas Aeneas.Std AspisR1CurrentCaller

theorem same {F C : Type} (adapter : AdapterRw.Ops) (ops : Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    SdkD_PairBatches.current adapter ops stage finish reserved query geo B std =
    Tx1Q_SameCut.callerDigest
      (Tx2I_Install.install adapter
        (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stage) reserved query geo)) finish)
      (Op5T_Concrete.current ops) reserved query geo B std := by
  unfold SdkD_PairBatches.current Tx1Q_SameCut.callerDigest
  rw [AuS1_Install.dictionary,Uni_Install.compose_tx1]

def transport {C H : Type} {installed : Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops C}
    {D D' : aspis_core.digest.Digest32 H} {hash : H}
    {semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (h : D=D')
    (r : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved) :
    Tx1Q_Execution.Run installed reserved query geo D' hash semantic pub proof split saved := by
  cases h
  exact r

theorem prepared {C H : Type} {installed : Ops} {reserved : Bool}
    {query : Port3_NativeQueryBody.Ops} {geo : Port3_NativeGeometryBody.Ops C}
    {D D' : aspis_core.digest.Digest32 H} {hash : H}
    {semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public}
    {pub proof : Slice U8} {split : Usize} {saved : alloc.vec.Vec U8}
    (h : D=D')
    (r : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved) :
    (transport h r).p=r.p := by
  cases h
  rfl

#print axioms same
#print axioms prepared
end AspisR1.PFin_Digest
end
