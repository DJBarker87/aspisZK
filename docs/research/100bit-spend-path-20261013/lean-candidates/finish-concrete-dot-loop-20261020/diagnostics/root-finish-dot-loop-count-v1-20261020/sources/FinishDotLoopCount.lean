import FinishDotConcreteOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotConcreteOps
open AspisR1CurrentWide.Proof AspisR1FinishDotSourceABI AspisR1FinishRelationCurrent

theorem successful_concrete_query_dot_count {W : Type}
    (base : FinishOps W PushState) (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (fm : Slice U8) (ws : Slice aspis_core.field.QM31) (out : FinishE)
    (hrun : verifier.finish_query_dot (withConcreteDot base rawFn) fm ws = .ok (.Ok out)) :
    ∃ final : PushState,
      final.count.val=ws.len.val ∧ finishFromPush final=.ok out ∧ CanonicalFinish out := by
  obtain ⟨initial,final,hnew,hchain,hfinish⟩ :=
    FinishCandidateDotTrace.finish_success_trace (withConcreteDot base rawFn) fm ws out hrun
  have hzero : initial=EbyKNewToPushStateABI.pushZero :=
    Result.ok.inj (hnew.symm.trans sourceNewDot_zero)
  let Inv : Nat → PushState → Prop := fun j s => s.count.val=j
  have hinitial : Inv 0 initial := by
    rw [hzero]
    rfl
  have hfinal := FinishCandidateDotTrace.chain_invariant
    (withConcreteDot base rawFn) fm ws Inv (by
      intro j j1 s s1 x q hactive hread hweight hpush hinc hinv
      have hcount := concrete_dot_push_count base rawFn s s1 x q hpush
      have hval := UScalar.add_equiv j 1#usize
      have hinc' : UScalar.add j 1#usize=.ok j1 := hinc
      rw [hinc'] at hval
      have hj1 : j1.val=j.val+1 := hval.2.1
      change s1.count.val=j1.val
      change s.count.val=j.val at hinv
      rw [hcount,hinv,hj1]) hchain hinitial
  exact ⟨final,hfinal,hfinish,(finishFromPush_success_canonical final out hfinish).1⟩

#print axioms successful_concrete_query_dot_count
end AspisR1FinishDotConcreteOps
