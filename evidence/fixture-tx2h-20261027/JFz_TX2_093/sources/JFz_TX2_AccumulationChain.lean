import JFz_TX2_AccumulateStep
import JFz_TX2_Gates
import JFz_TX2_Nodes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_AccumulationChain
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)

def query (n : Nat) : Fin 12 := ⟨n%12,Nat.mod_lt _ (by omega)⟩
def updates (seed : Port3_NativeQueryBody.Ops) : Nat → Result (verifier.Accumulator × verifier.BatchedWeights)
  | 0 => ok (JFo_Prepared.accumulator,JFo_Pending.value)
  | n+1 => do
    let (a,b) ← updates seed n
    Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
      JFo_Prepared.value a (JFz_TX2_Nodes.value (query n)) (JFz_TX2_Gates.lineValue (query n)) b

def Invariant (n : Nat) (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop :=
  a.weights=JFo_Prepared.accumulator.weights ∧ a.next.val=10+n ∧
  Port4C_QueryArithmetic.CanonE a.rhs ∧ Port3_FlushInstall.Canonical a.power ∧
  ∃ sum : Sum, PushTrace JFn_PendingHistory.old (Port3_RowsInstall.toBW b) sum ∧
    Progress n 0 (Port3_RowsInstall.toBW b)

theorem initial : Invariant 0 JFo_Prepared.accumulator JFo_Pending.value :=
  ⟨rfl,rfl,JFn_AccumulatorCanonical.rhs,JFn_AccumulatorCanonical.power,
    JFn_PendingHistory.sum,JFn_PendingHistory.trace,JFn_PendingHistory.progress⟩

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (n : Nat) (bound : n≤12) :
    ∃ a b, updates seed n=ok (a,b) ∧ Invariant n a b := by
  induction n with
  | zero => exact ⟨_,_,rfl,initial⟩
  | succ n ih =>
    obtain ⟨a,b,run,weights,next,crhs,cpower,sum,history,phase⟩ := ih (by omega)
    obtain ⟨out,after,sumOut,step,hw,hn,cr,cp,ht,hp⟩ :=
      JFz_TX2_AccumulateStep.source seed a b sum n (JFz_TX2_Nodes.value (query n))
        (JFz_TX2_Gates.lineValue (query n)) weights (by omega) (by omega) crhs cpower
        (JFz_TX2_Gates.canonical err geometrySeed (query n)) history phase
    refine ⟨out,after,?_,hw,?_,cr,cp,sumOut,ht,hp⟩
    · simp only [updates,run,bind_tc_ok]
      exact step
    · omega

theorem twelve {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) :
    ∃ a b, updates seed 12=ok (a,b) ∧ Invariant 12 a b ∧ a.next=22#usize := by
  obtain ⟨a,b,run,inv⟩ := source err geometrySeed seed 12 (by omega)
  exact ⟨a,b,run,inv,UScalar.eq_of_val_eq inv.2.1⟩
#print axioms initial
#print axioms source
#print axioms twelve
end AspisR1.JFz_TX2_AccumulationChain
end
