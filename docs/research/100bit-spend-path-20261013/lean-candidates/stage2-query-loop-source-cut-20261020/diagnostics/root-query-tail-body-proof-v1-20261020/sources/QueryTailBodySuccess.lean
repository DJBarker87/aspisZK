import QueryTailExplicitQuery
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

def retained (old : verifier.BatchedWeights) (o : Option verifier.BatchedWeights) :
    verifier.BatchedWeights := match o with | some v => v | none => old

theorem body_cont (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a a1 : verifier.Accumulator) (pending pending1 : verifier.BatchedWeights)
    (h : verifier.candidate.tx2_query_tail_loop.body query proof p g obs geometry a pending =
      .ok (.cont (a1,pending1))) :
    a.next < 22#usize ∧ ∃ o,
      query proof p a g obs geometry (some pending) = .ok (.Ok (),a1,o) ∧
      pending1 = retained pending o := by
  unfold verifier.candidate.tx2_query_tail_loop.body at h
  by_cases ha : a.next < 22#usize
  · simp only [ha,↓reduceIte] at h
    obtain ⟨triple,hquery,h⟩ := bind_success _ _ _ h
    rcases triple with ⟨r,a2,o⟩
    cases r with
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      have he : (a2,retained pending o) = (a1,pending1) := by simpa [retained] using h
      have hea := congrArg Prod.fst he
      have hep := congrArg Prod.snd he
      subst a2
      exact ⟨ha,o,hquery,hep.symm⟩
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  · simp [ha] at h

theorem body_done_none (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a a1 : verifier.Accumulator) (pending pending1 : verifier.BatchedWeights)
    (h : verifier.candidate.tx2_query_tail_loop.body query proof p g obs geometry a pending =
      .ok (.done (a1,pending1,none))) :
    ¬a.next < 22#usize ∧ a1 = a ∧ pending1 = pending := by
  unfold verifier.candidate.tx2_query_tail_loop.body at h
  by_cases ha : a.next < 22#usize
  · simp only [ha,↓reduceIte] at h
    obtain ⟨triple,hquery,h⟩ := bind_success _ _ _ h
    rcases triple with ⟨r,a2,o⟩
    cases r with
    | Ok unit => cases unit; simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  · simp only [ha,↓reduceIte] at h
    have he : (a,pending,(none : Option (core.result.Result
        (verifier.Prepared × verifier.Accumulator × verifier.BatchedWeights) verifier.Error))) =
      (a1,pending1,none) := by simpa using h
    exact ⟨ha,(congrArg (fun t => t.1) he).symm,(congrArg (fun t => t.2.1) he).symm⟩

theorem body_done_not_ok (query : Query) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (a a1 : verifier.Accumulator) (pending pending1 : verifier.BatchedWeights)
    (out : verifier.Prepared × verifier.Accumulator × verifier.BatchedWeights)
    (h : verifier.candidate.tx2_query_tail_loop.body query proof p g obs geometry a pending =
      .ok (.done (a1,pending1,some (.Ok out)))) : False := by
  unfold verifier.candidate.tx2_query_tail_loop.body at h
  by_cases ha : a.next < 22#usize
  · simp only [ha,↓reduceIte] at h
    obtain ⟨triple,hquery,h⟩ := bind_success _ _ _ h
    rcases triple with ⟨r,a2,o⟩
    cases r with
    | Ok unit => cases unit; simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  · simp [ha] at h
#print axioms body_cont
#print axioms body_done_none
#print axioms body_done_not_ok
end AspisR1Stage2QueryTailCut.QueryTailProof
