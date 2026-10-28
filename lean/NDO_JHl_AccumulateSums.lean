import NDO_JFz_TX2_AccumulateStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_AccumulateSums
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_RowsInstall (toBW toK fromBW)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)

/-- The existing native basis/row and arithmetic theorems applied to the
actual caller's preparation, weights and pending history. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (p : verifier.Prepared)
    (old : S8OwnedP6Finish.Weights)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum) (t : Nat)
    (node : U32) (value : SAQ_WideABI.E)
    (size : a.weights.val.length=64) (next : a.next.val≤22) (terms : t<22)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (crho : Port3_FlushInstall.Canonical p.rho)
    (canonical : Port4C_QueryArithmetic.CanonE value)
    (history : PushTrace old (toBW b) sum) (phase : Progress t 0 (toBW b)) :
    ∃ (basis : Array U32 256#usize), ∃ out after sumOut,
      (∀ i : Fin 64, S7JoinBasisMachine.decode (S7JoinBasisBlock.cell basis i.val)=
        AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) i.val) ∧
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
        p a node value b=ok (out,after) ∧
      out.weights=a.weights ∧ out.next.val=a.next.val+1 ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      PushTrace old (toBW after) sumOut ∧ Progress (t+1) 0 (toBW after) ∧
      ∀ i k, sumOut i k=if i<64 then sum i k+
        (S7Kani2OwnedRowRefinement.powerLimb (toK a.power) k).val*
          (S7JoinBasisBlock.cell basis i).val else sum i k := by
  obtain ⟨basis,hbasis,cbasis,meaning⟩ := JFn_Basis.source seed node
  have cp : S7JoinBackendCarriers.Canonical (toK a.power) := by
    intro j
    fin_cases j
    · exact cpower.1
    · exact cpower.2.1
    · exact cpower.2.2.1
    · exact cpower.2.2.2
  obtain ⟨rows,sumOut,hrows,trace,progress,sums⟩ := Port4C_RowMeaning.rows
    (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed)) old
    a.weights b sum basis a.power a.next t size next cp cbasis history phase
  have rowsCall : Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1
      (JFn_ArrayBuilder.ops seed) {start:=0#usize,«end»:=64#usize}
      a.weights a.power a.next b 64#usize basis=ok (fromBW rows) := hrows
  obtain ⟨product,hproduct,cproduct⟩ := JFn_QueryArithmeticTotal.mulE value a.power canonical cpower
  obtain ⟨rhs,hrhs,crhs'⟩ := JFn_QueryArithmeticTotal.add a.rhs product crhs cproduct
  obtain ⟨power,hpower,cpower'⟩ := JFn_QueryArithmeticTotal.mulK a.power p.rho cpower crho
  have hp : (JFn_ArrayBuilder.ops seed).op3 value a.power=ok product := hproduct
  have hr : (JFn_ArrayBuilder.ops seed).op2 a.rhs product=ok rhs := hrhs
  have hq : (JFn_ArrayBuilder.ops seed).op9 a.power p.rho=ok power := hpower
  let inc := Usize.wrapping_add (fromBW rows).terms 1#usize
  have hv : inc.val=t+1 := by
    change (Usize.wrapping_add rows.terms 1#usize).val=t+1
    rw [Port3_Wrapping.increment rows.terms (by rw [progress.1];omega),progress.1]
  have nv : (Usize.wrapping_add a.next 1#usize).val=a.next.val+1 :=
    Port3_Wrapping.increment a.next (by omega)
  refine ⟨basis,{a with rhs,power,next:=Usize.wrapping_add a.next 1#usize},
    {fromBW rows with terms:=inc},sumOut,meaning,?_,rfl,nv,crhs',cpower',?_,?_,sums⟩
  · rw [Port4C_BasisMeaning.factor _ _ _ _ _ _ size]
    simp only [hbasis,rowsCall,hp,hr,hq,bind_tc_ok,lift,inc,
      show (JFn_ArrayBuilder.ops seed).op15 11#u16 a.next rhs=ok () from rfl]
  · exact PushTrace.counter trace inc
  · exact S7JoinRowsTrace.next_query_progress t rows inc hv progress
#print axioms source
end AspisR1.JHl_AccumulateSums
end
