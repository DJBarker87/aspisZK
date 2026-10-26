import Tx1Q_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Rebind
open Aeneas Aeneas.Std
open AspisR1CurrentCaller

def run {C H : Type} {installed : Ops} {reserved : Bool}
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
    (run h r).p=r.p := by
  cases h
  rfl

#print axioms prepared
end AspisR1.SAP_Rebind
end
