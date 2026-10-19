import QueryTailLoopTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2QueryTailCut.QueryTailProof
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem successful_tail_trace (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (advance : ∀ (a a1 : verifier.Accumulator) (pending : verifier.BatchedWeights)
      (o : Option verifier.BatchedWeights),
      query proof p a g obs geometry (some pending) = .ok (.Ok (),a1,o) →
      a1.next.val = a.next.val + 1)
    (a out : verifier.Accumulator) (pending pendingOut : verifier.BatchedWeights)
    (pout : verifier.Prepared) (ha : a.next.val ≤ 22)
    (hrun : verifier.candidate.tx2_query_tail query proof p a g obs geometry pending =
      .ok (.Ok (pout,out,pendingOut))) :
    pout = p ∧ out.next.val = 22 ∧
    Chain query proof p g obs geometry a pending out pendingOut (22-a.next.val) := by
  unfold verifier.candidate.tx2_query_tail at hrun
  obtain ⟨triple,hloop,h⟩ := bind_success _ _ _ hrun
  rcases triple with ⟨out1,pending1,ret⟩
  have trace := loop_success_trace query proof p g obs geometry advance a out1 pending pending1 ret ha hloop
  rcases trace with ⟨err,herr⟩ | ⟨hnone,hchain⟩
  · subst ret
    have hbad : core.result.Result.Err err =
      core.result.Result.Ok (pout,out,pendingOut) := Result.ok.inj h
    cases hbad
  · subst ret
    have he := core.result.Result.Ok.inj (Result.ok.inj h)
    have hp := congrArg Prod.fst he
    have ho := congrArg (fun t => t.2.1) he
    have hb := congrArg (fun t => t.2.2) he
    change p = pout at hp
    change out1 = out at ho
    change pending1 = pendingOut at hb
    subst pout; subst out1; subst pending1
    exact ⟨rfl,chain_end query proof p g obs geometry hchain,hchain⟩

theorem stage2_twelve_calls (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (advance : ∀ (a a1 : verifier.Accumulator) (pending : verifier.BatchedWeights)
      (o : Option verifier.BatchedWeights),
      query proof p a g obs geometry (some pending) = .ok (.Ok (),a1,o) →
      a1.next.val = a.next.val + 1)
    (a out : verifier.Accumulator) (pending pendingOut : verifier.BatchedWeights)
    (pout : verifier.Prepared) (start : a.next.val = 10)
    (hrun : verifier.candidate.tx2_query_tail query proof p a g obs geometry pending =
      .ok (.Ok (pout,out,pendingOut))) :
    pout = p ∧ out.next.val = 22 ∧
    Chain query proof p g obs geometry a pending out pendingOut 12 := by
  have h := successful_tail_trace query proof p g obs geometry advance a out pending pendingOut pout (by omega) hrun
  simpa only [start] using h
#print axioms successful_tail_trace
#print axioms stage2_twelve_calls
end AspisR1Stage2QueryTailCut.QueryTailProof
