import Stage2FinishBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.Port3_FinishControl
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem guard_success {A : Type} (b : Bool) (e : verifier.Error)
    (tail : Result (core.result.Result A verifier.Error)) (v : A)
    (h : (if b then ok (.Err e) else tail) = ok (.Ok v)) :
    b = false ∧ tail = ok (.Ok v) := by
  cases b
  · exact ⟨rfl,h⟩
  · cases h

/-- A successful emitted relation round enforces its boundary and returns its
polynomial evaluation. No arithmetic semantics are assumed here. -/
theorem round_success (ops : FinishOps W) (poly : Slice U8) (alpha claim out : E)
    (round : Usize)
    (h : verifier.finishRelationRoundWithOps ops poly alpha claim round = ok (.Ok out)) :
    ∃ c0 c4 lhs quarter rhs,
      ops.field poly 0#usize = ok c0 ∧ ops.field poly 4#usize = ok c4 ∧
      ops.add c0 c4 = ok lhs ∧ ops.quarter = ok quarter ∧
      ops.mulM claim quarter = ok rhs ∧ ops.ne lhs rhs = ok false ∧
      ops.polynomial poly alpha = ok out := by
  unfold verifier.finishRelationRoundWithOps at h
  obtain ⟨c0, hc0, h⟩ := bind_success _ _ _ h
  obtain ⟨c4, hc4, h⟩ := bind_success _ _ _ h
  obtain ⟨lhs, hlhs, h⟩ := bind_success _ _ _ h
  obtain ⟨quarter, hquarter, h⟩ := bind_success _ _ _ h
  obtain ⟨rhs, hrhs, h⟩ := bind_success _ _ _ h
  iterate 4 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := bind_success _ _ _ h
  obtain ⟨hb, h⟩ := guard_success _ _ _ _ h
  obtain ⟨value, hv, h⟩ := bind_success _ _ _ h
  iterate 2 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  exact ⟨c0,c4,lhs,quarter,rhs,hc0,hc4,hlhs,hquarter,hrhs,hb ▸ hbad,hv⟩

/-- Successful try propagation exposes an Ok callee, never an Err callee. -/
theorem try_success {A B : Type} (r : core.result.Result A verifier.Error)
    (k : A → Result (core.result.Result B verifier.Error)) (out : B)
    (h : (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue v => k v
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          B (core.convert.FromSame verifier.Error) residual) = ok (.Ok out)) :
    ∃ v, r = .Ok v ∧ k v = ok (.Ok out) := by
  cases r with
  | Ok v => exact ⟨v,rfl,h⟩
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h

/-- The S2 branch supplies the two successful relation rounds, the pair
comparison, and the final dot comparison on exactly the consumed accumulator. -/
theorem finish_success (ops : FinishOps W) (v : verifier.View)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (two : ops.folds p.variant = ok 2#usize)
    (h : verifier.finishRelationWithOps ops v p a obs = ok (.Ok ())) :
    ∃ alpha0 claim0 alpha1 claim1 weights alphas pair actual,
      Array.index_usize p.alpha 0#usize = ok alpha0 ∧
      verifier.finishRelationRoundWithOps ops v.round0 alpha0 p.claim 0#usize = ok (.Ok claim0) ∧
      Array.index_usize p.alpha 1#usize = ok alpha1 ∧
      verifier.finishRelationRoundWithOps ops v.round1 alpha1 claim0 1#usize = ok (.Ok claim1) ∧
      ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas ∧
      ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair) ∧
      ops.ne pair claim1 = ok false ∧
      ops.dot v.final_message (alloc.vec.Vec.deref a.weights) = ok (.Ok actual) ∧
      a.next = 22#usize ∧ ops.ne actual a.rhs = ok false := by
  unfold verifier.finishRelationWithOps at h
  obtain ⟨alpha0, ha0, h⟩ := bind_success _ _ _ h
  obtain ⟨r0, hr0, h⟩ := bind_success _ _ _ h
  cases r0 with
  | Err err =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok claim0 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨folds, hfolds, h⟩ := bind_success _ _ _ h
    have hf : folds = 2#usize := Result.ok.inj (hfolds.symm.trans two)
    subst folds
    simp only [ite_true] at h
    obtain ⟨alpha1, ha1, h⟩ := bind_success _ _ _ h
    obtain ⟨r1, hr1, h⟩ := bind_success _ _ _ h
    cases r1 with
    | Err err =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok claim1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨rw, hrw, h⟩ := bind_success _ _ _ h
      cases rw with
      | Err err =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok weights =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
        obtain ⟨alphas, has, h⟩ := bind_success _ _ _ h
        obtain ⟨rp, hrp, h⟩ := bind_success _ _ _ h
        cases rp with
        | Err err =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
        | Ok pair =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          iterate 2 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
          obtain ⟨bad, hbad, h⟩ := bind_success _ _ _ h
          obtain ⟨hb, h⟩ := guard_success _ _ _ _ h
          obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
          obtain ⟨rd, hrd, h⟩ := bind_success _ _ _ h
          cases rd with
          | Err err =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at h
            cases h
          | Ok actual =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
            iterate 2 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
            have hn : a.next = 22#usize := by
              split at h
              · cases h
              · rename_i heq
                simpa only [bne_iff_ne, not_not] using heq
            have hn' : (a.next != 22#usize) = false := by simp only [hn, bne_self_eq_false]
            rw [hn'] at h
            obtain ⟨bad1, hbad1, h⟩ := bind_success _ _ _ h
            obtain ⟨hb1, h⟩ := guard_success _ _ _ _ h
            exact ⟨alpha0,claim0,alpha1,claim1,weights,alphas,pair,actual,
              ha0,hr0,ha1,hr1,hrw,has,hrp,hb ▸ hbad,hrd,hn,hb1 ▸ hbad1⟩
#print axioms bind_success
#print axioms guard_success
#print axioms round_success
#print axioms try_success
#print axioms finish_success
end AspisR1.Port3_FinishControl

#print axioms AspisR1.Port3_FinishControl.round_success
#print axioms AspisR1.Port3_FinishControl.finish_success
