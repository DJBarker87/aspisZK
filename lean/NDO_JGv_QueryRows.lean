import NDO_JGv_QueryRowsStep
import NDO_JGv_QueryScalars
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryRows
open Aeneas Aeneas.Std Result AspisR1Stage2
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev F := ZMod 2147483647

def weights : Nat → Nat → Fin 4 → F
  | 0,j,k => (JFn_PendingHistory.sum j k : F)
  | n+1,j,k => weights n j k+
      (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK (JGv_QueryScalars.power n)) k).val*
      AspisCircleTensorBinding.naturalLineValue
        (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query n))) j

def Invariant (n : Nat) (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop :=
  a.weights=JFo_Prepared.accumulator.weights ∧ a.next.val=10+n ∧
  Port4C_QueryArithmetic.CanonE a.rhs ∧ Port3_FlushInstall.Canonical a.power ∧
  a.rhs=JGv_QueryScalars.rhs n ∧ a.power=JGv_QueryScalars.power n ∧
  ∃ sum : Sum,PushTrace JFn_PendingHistory.old (Port3_RowsInstall.toBW b) sum ∧
    Progress n 0 (Port3_RowsInstall.toBW b) ∧
    ∀ j,j<64 → ∀ k,(sum j k : F)=weights n j k

theorem initial : Invariant 0 JFo_Prepared.accumulator JFo_Pending.value := by
  exact ⟨rfl,rfl,JFn_AccumulatorCanonical.rhs,JFn_AccumulatorCanonical.power,rfl,rfl,
    JFn_PendingHistory.sum,JFn_PendingHistory.trace,JFn_PendingHistory.progress,fun _ _ _=>rfl⟩
#print axioms initial

theorem step {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (n : Nat) (hn : n<12)
    (state : JFz_TX2_ChainStep.Pair) (inv : Invariant n state.1 state.2) :
    ∃ out,JFz_TX2_ChainStep.transition seed n state=ok out ∧ Invariant (n+1) out.1 out.2 := by
  rcases state with ⟨a,b⟩
  change Invariant n a b at inv
  obtain ⟨hw,hnxt,cr,cp,hr,hp,sum,history,phase,hm⟩ := inv
  obtain ⟨out,after,sumOut,basis,call,ow,onext,ocr,ocp,trace,progress,meaning,sums⟩ :=
    JGv_QueryRowsStep.source seed a b sum n (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query n))
      (JFz_TX2_Gates.lineValue (JFz_TX2_ChainStep.query n)) hw (by omega) hn cr cp
      (JFz_TX2_Gates.canonical err geometry _) history phase
  have scalars := JGv_QueryScalars.step seed n hn a b out after hw hr hp call
  refine ⟨(out,after),call,ow,(by change out.next.val=10+(n+1);omega),ocr,ocp,scalars.1,scalars.2,sumOut,trace,progress,?_⟩
  intro j hj k
  rw [sums j k,if_pos hj,Nat.cast_add,Nat.cast_mul,hm j hj k,weights,hp]
  congr 1
  congr 1
  exact meaning ⟨j,hj⟩
#print axioms step

theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (n : Nat) (hn : n≤12)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (call : JFz_TX2_AccumulationChain.updates seed n=ok (a,b)) :
    Invariant n a b := by
  obtain ⟨out,run,inv⟩ := JFz_TX2_Sequence.source (JFz_TX2_ChainStep.transition seed)
    (JFo_Prepared.accumulator,JFo_Pending.value)
    (fun n state=>Invariant n state.1 state.2) 12 initial (step err geometry seed) n hn
  have same := Result.ok.inj (run.symm.trans call)
  cases same
  exact inv
#print axioms source
end AspisR1.JGv_QueryRows
end
