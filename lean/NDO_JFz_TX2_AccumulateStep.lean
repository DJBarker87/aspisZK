import NDO_JFn_Accumulate
import NDO_JFn_AccumulationFlush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_AccumulateStep
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_RowsInstall (toBW toK fromBW)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)

theorem source (seed : Port3_NativeQueryBody.Ops)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights) (sum : Sum) (t : Nat)
    (node : U32) (value : SAQ_WideABI.E)
    (weights : a.weights=JFo_Prepared.accumulator.weights)
    (next : a.next.val≤22) (terms : t<12)
    (crhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (cpower : Port3_FlushInstall.Canonical a.power)
    (canonical : Port4C_QueryArithmetic.CanonE value)
    (history : PushTrace JFn_PendingHistory.old (toBW b) sum)
    (phase : Progress t 0 (toBW b)) :
    ∃ out after sumOut,
      Port3_NativeQueryBody.verifier.accumulate_batched_with_node (JFn_ArrayBuilder.ops seed)
        JFo_Prepared.value a node value b=ok (out,after) ∧
      out.weights=JFo_Prepared.accumulator.weights ∧ out.next.val=a.next.val+1 ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power ∧
      PushTrace JFn_PendingHistory.old (toBW after) sumOut ∧ Progress (t+1) 0 (toBW after) := by
  obtain ⟨basis,hbasis,cbasis,_⟩ := JFn_Basis.source seed node
  have size : a.weights.val.length=64 := by rw [weights];exact JFo_Prepared.weights_length
  have cp : S7JoinBackendCarriers.Canonical (toK a.power) := by
    intro j
    fin_cases j
    · exact cpower.1
    · exact cpower.2.1
    · exact cpower.2.2.1
    · exact cpower.2.2.2
  obtain ⟨rows,sumOut,hrows,trace,progress,_⟩ := Port4C_RowMeaning.rows
    (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed)) JFn_PendingHistory.old
    a.weights b sum basis a.power a.next t size next cp cbasis history phase
  have rowsCall : Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1
      (JFn_ArrayBuilder.ops seed) {start:=0#usize,«end»:=64#usize}
      a.weights a.power a.next b 64#usize basis=ok (fromBW rows) := hrows
  obtain ⟨product,hproduct,cproduct⟩ := JFn_QueryArithmeticTotal.mulE value a.power canonical cpower
  obtain ⟨rhs,hrhs,crhs'⟩ := JFn_QueryArithmeticTotal.add a.rhs product crhs cproduct
  obtain ⟨power,hpower,cpower'⟩ := JFn_QueryArithmeticTotal.mulK a.power JFo_Prepared.value.rho cpower JFn_AccumulatorCanonical.rho
  have hp : (JFn_ArrayBuilder.ops seed).op3 value a.power=ok product := hproduct
  have hr : (JFn_ArrayBuilder.ops seed).op2 a.rhs product=ok rhs := hrhs
  have hq : (JFn_ArrayBuilder.ops seed).op9 a.power JFo_Prepared.value.rho=ok power := hpower
  let inc := Usize.wrapping_add (fromBW rows).terms 1#usize
  have hv : inc.val=t+1 := by
    change (Usize.wrapping_add rows.terms 1#usize).val=t+1
    rw [Port3_Wrapping.increment rows.terms (by rw [progress.1];omega),progress.1]
  have nv : (Usize.wrapping_add a.next 1#usize).val=a.next.val+1 :=
    Port3_Wrapping.increment a.next (by omega)
  refine ⟨{a with rhs,power,next:=Usize.wrapping_add a.next 1#usize},
    {fromBW rows with terms:=inc},sumOut,?_,weights,nv,crhs',cpower',?_,?_⟩
  · rw [Port4C_BasisMeaning.factor _ _ _ _ _ _ size]
    simp only [hbasis,rowsCall,hp,hr,hq,bind_tc_ok,lift,inc,
      show (JFn_ArrayBuilder.ops seed).op15 11#u16 a.next rhs=ok () from rfl]
  · exact PushTrace.counter trace inc
  · exact S7JoinRowsTrace.next_query_progress t rows inc hv progress
#print axioms source
end AspisR1.JFz_TX2_AccumulateStep
end
