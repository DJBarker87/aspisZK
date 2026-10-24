import Port4C_BasisMeaning

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_Accumulation
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_RowsInstall (toK toBW fromBW)
open Port3_PushFrame (bind_success)
open S7Kani3CallerTrace (PushTrace Sum)
open S7JoinRowsTrace (Progress)
abbrev K := aspis_core.field.QM31

private theorem backend_std (ops : Ops) (backend : Port4C_BasisOuter.SessionABasis ops) :
    Port4C_BasisOuter.SessionABasis (Port4C_RowStd.install ops) := by
  exact ⟨backend.s3_s4_mul,backend.s3_s4_sub,backend.s3_s4_double,backend.zero,backend.one⟩

/-- Full current native basis/row/terms portion, interpreted from the SAME
accepted accumulation. Basis success, canonicality, row history and phase
are derived rather than supplied as successful child observations. -/
theorem rows (ops : Ops) (backend : Port4C_BasisOuter.SessionABasis ops)
    (old : S8OwnedP6Finish.Weights) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (node : U32) (value : Stage2E) (sum : Sum) (t : Nat)
    (size : a.weights.val.length=64) (nextBound : a.next.val≤22) (termBound : t<22)
    (powerCanonical : S7JoinBackendCarriers.Canonical (toK a.power))
    (history : PushTrace old (toBW b) sum) (phase : Progress t 0 (toBW b))
    (h : verifier.accumulate_batched_with_node (Port4C_RowStd.install ops)
      p a node value b=ok (out,bout)) :
    ∃ sumOut,
      PushTrace old (toBW bout) sumOut ∧ Progress (t+1) 0 (toBW bout) ∧
      ∀ i, i<64 → ∀ k : Fin 4,
        (sumOut i k : ZMod AspisCircleGroupOrder.P)=(sum i k : ZMod AspisCircleGroupOrder.P)+
          (S7Kani2OwnedRowRefinement.powerLimb (toK a.power) k).val*
            AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) i := by
  rw [Port4C_BasisMeaning.factor _ p a node value b size] at h
  obtain ⟨basis,hbasis,h⟩ := bind_success _ _ _ h
  obtain ⟨expected,run,canonical,meaning⟩ := Port4C_BasisMeaning.total
    (Port4C_RowStd.install ops) (backend_std ops backend) node
  have same : basis=expected := Result.ok.inj (hbasis.symm.trans run)
  subst basis
  obtain ⟨mid,hrows,h⟩ := bind_success _ _ _ h
  obtain ⟨after,sumOut,native,trace,progress,sums⟩ := Port4C_RowMeaning.rows ops old a.weights b sum
    expected a.power a.next t size nextBound powerCanonical canonical history phase
  have same : mid=fromBW after := Result.ok.inj (hrows.symm.trans native)
  subst mid
  obtain ⟨terms,hterms,h⟩ := bind_success _ _ _ h
  have termsValue : terms.val=t+1 := by
    have same := Result.ok.inj hterms
    rw [←same,Port3_Wrapping.increment after.terms (by have hp := progress.1; omega),progress.1]
  iterate 5 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  refine ⟨sumOut,.counter trace terms,S7JoinRowsTrace.next_query_progress t after terms termsValue progress,?_⟩
  intro i hi k
  rw [sums i k,if_pos hi,Nat.cast_add,Nat.cast_mul]
  change (sum i k : ZMod AspisCircleGroupOrder.P)+
    (S7Kani2OwnedRowRefinement.powerLimb (toK a.power) k).val*
      S7JoinBasisMachine.decode (S7JoinBasisBlock.cell expected i)=_
  rw [meaning ⟨i,hi⟩]

#print axioms backend_std
#print axioms rows
end AspisR1.Port4C_Accumulation
end
