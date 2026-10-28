import NDO_JFz_TX2_Sequence
import NDO_JFz_TX2_Gates
import NDO_JFz_TX2_Nodes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_ChainStep
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
def query (n : Nat) : Fin 12 := ⟨n%12,Nat.mod_lt _ (by omega)⟩
abbrev Pair := verifier.Accumulator × verifier.BatchedWeights

def transition (seed : Port3_NativeQueryBody.Ops) (n : Nat) (state : Pair) : Result Pair :=
  Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
    JFo_Prepared.value state.1 (JFz_TX2_Nodes.value (query n))
      (JFz_TX2_Gates.lineValue (query n)) state.2

def updates (seed : Port3_NativeQueryBody.Ops) (n : Nat) : Result Pair :=
  JFz_TX2_Sequence.run (transition seed) (JFo_Prepared.accumulator,JFo_Pending.value) n

def Invariant (n : Nat) (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop :=
  a.weights=JFo_Prepared.accumulator.weights ∧ a.next.val=10+n ∧
  Port4C_QueryArithmetic.CanonE a.rhs ∧ Port3_FlushInstall.Canonical a.power ∧
  ∃ sum : Sum, PushTrace JFn_PendingHistory.old (Port3_RowsInstall.toBW b) sum ∧
    Progress n 0 (Port3_RowsInstall.toBW b)

theorem initial : Invariant 0 JFo_Prepared.accumulator JFo_Pending.value :=
  ⟨rfl,rfl,JFn_AccumulatorCanonical.rhs,JFn_AccumulatorCanonical.power,
    JFn_PendingHistory.sum,JFn_PendingHistory.trace,JFn_PendingHistory.progress⟩


theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (n : Nat) (hn : n<12)
    (state : Pair) (inv : Invariant n state.1 state.2) :
    ∃ out : Pair,transition seed n state=ok out ∧ Invariant (n+1) out.1 out.2 := by
  rcases state with ⟨a,b⟩
  change Invariant n a b at inv
  obtain ⟨weights,next,crhs,cpower,sum,history,phase⟩ := inv
  obtain ⟨out,after,sumOut,step,hw,hn',cr,cp,ht,hp⟩ :=
    JFz_TX2_AccumulateStep.source seed a b sum n (JFz_TX2_Nodes.value (query n))
      (JFz_TX2_Gates.lineValue (query n)) weights (by omega) hn crhs cpower
      (JFz_TX2_Gates.canonical err geometrySeed (query n)) history phase
  refine ⟨(out,after),step,hw,?_,cr,cp,sumOut,ht,hp⟩
  change out.next.val=10+(n+1)
  omega
#print axioms initial
#print axioms source
end AspisR1.JFz_TX2_ChainStep
end
