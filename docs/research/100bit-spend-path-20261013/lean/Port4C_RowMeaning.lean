import Port4C_RowLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_RowMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_RowsInstall (toK toBW fromBW toWeights)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev K := aspis_core.field.QM31

/-- All64 CURRENT native row writes produce the existing concrete owned
push trace and exact sum update. History/phase are propagated by source
induction; they are not requested independently for each row. -/
theorem rows (ops : Ops) (old : S8OwnedP6Finish.Weights) (v : alloc.vec.Vec K)
    (b : verifier.BatchedWeights) (sum : Sum) (basis : Array U32 256#usize)
    (power : K) (next : Usize) (t : Nat)
    (size : v.val.length=64) (bound : next.val≤22)
    (canonical : S7JoinBackendCarriers.Canonical (toK power))
    (basisCanonical : S7JoinBasisCanonical.Canonical basis)
    (history : PushTrace old (toBW b) sum) (phase : Progress t 0 (toBW b)) :
    ∃ after sumOut,
      verifier.accumulate_batched_with_node_loop1 (Port4C_RowStd.install ops)
        {start:=0#usize,«end»:=64#usize} v power next b 64#usize basis=ok (fromBW after) ∧
      PushTrace old after sumOut ∧ Progress t 64 after ∧
      ∀ i k, sumOut i k=if i<64 then
        sum i k+(S7Kani2OwnedRowRefinement.powerLimb (toK power) k).val*
          (S7JoinBasisBlock.cell basis i).val else sum i k := by
  have mappedSize : (toWeights v).val.length=64 := by simpa only [toWeights,List.length_map] using size
  obtain ⟨after,sumOut,run,trace,progress,sums⟩ := S7JoinRowsTrace.rows_exact old (toWeights v)
    (toBW b) sum basis (toK power) next 0#usize 64 t mappedSize bound (by decide)
    canonical basisCanonical history phase
  rw [S7Kani2AccumulatorLoop.extracted_loop_composition S7JoinRowsTrace.backend basis
    (toK power) next 64#usize 0#usize 64 (toWeights v,toBW b) (by decide) (by decide)] at run
  have native := Port4C_RowLoop.from_iterate ops v power next basis
    {start:=0#usize,«end»:=64#usize} b (fromBW after) 64 size (by decide) (by decide) run
  refine ⟨after,sumOut,native,trace,progress,?_⟩
  intro i k
  simpa only [show (0#usize).val=0 from rfl,Nat.zero_le,true_and] using sums i k

#print axioms rows
end AspisR1.Port4C_RowMeaning
end
