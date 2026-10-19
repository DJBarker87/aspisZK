import FinishCandidateRoundSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishRelationCurrent.FinishCandidateOuterSuccess
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem try_success {A B : Type} (r : core.result.Result A verifier.Error)
    (k : A → Result (core.result.Result B verifier.Error)) (out : B)
    (h : (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue v => k v
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          B (core.convert.FromSame verifier.Error) residual) = ok (.Ok out)) :
    ∃ v, r = .Ok v ∧ k v = ok (.Ok out) := by
  cases r with
  | Ok v => exact ⟨v, rfl, by simpa only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] using h⟩
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h

theorem s2_success_calls {W D : Type} (ops : FinishOps W D)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant = transport.Variant.S2)
    (h : verifier.finish_relation ops v p a obs = ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2 w sliced pair actual,
      Array.index_usize p.alpha 0#usize = ok alpha0 ∧
      verifier.finish_relation_round ops v.round0 alpha0 p.claim 0#usize = ok (.Ok claim1) ∧
      Array.index_usize p.alpha 1#usize = ok alpha1 ∧
      verifier.finish_relation_round ops v.round1 alpha1 claim1 1#usize = ok (.Ok claim2) ∧
      ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok w) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.WideExact))
        p.alpha { «end» := 2#usize } = ok sliced ∧
      ops.pair w sliced v.final_message p.kappa = ok (.Ok pair) ∧
      core.cmp.PartialEq.ne.trait_default
        (aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact ops) pair claim2 = ok false ∧
      verifier.mark obs verifier.Phase.Relation = ok () ∧
      verifier.finish_query_dot ops v.final_message (alloc.vec.Vec.deref a.weights) = ok (.Ok actual) ∧
      (a.next != 22#usize) = false ∧
      core.cmp.PartialEq.ne.trait_default
        (aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact ops) actual a.rhs = ok false ∧
      verifier.mark obs verifier.Phase.Final = ok () := by
  have hf : transport.Variant.folds p.variant = ok 2#usize := by
    norm_num [hv, transport.Variant.folds, transport.Variant.Insts.CoreCmpPartialEqVariant.eq, read_discriminant, transport.Variant.read_discriminant]
  unfold verifier.finish_relation at h
  obtain ⟨alpha0, ha0, h⟩ := bind_success _ _ _ h
  obtain ⟨r0, hr0, h⟩ := bind_success _ _ _ h
  cases r0 with
  | Err err =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok claim1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    rw [hf] at h
    simp only [bind_tc_ok, ↓reduceIte] at h
    obtain ⟨alpha1, ha1, h⟩ := bind_success _ _ _ h
    obtain ⟨r1, hr1, h⟩ := bind_success _ _ _ h
    cases r1 with
    | Err err =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok claim2 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨rwgt, hwgt, h⟩ := bind_success _ _ _ h
      cases rwgt with
      | Err err =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok w =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
        obtain ⟨sliced, hsliced, h⟩ := bind_success _ _ _ h
        obtain ⟨rpair, hpair, h⟩ := bind_success _ _ _ h
        cases rpair with
        | Err err =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
        | Ok pair =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          obtain ⟨_, _, h⟩ := bind_success _ _ _ h
          obtain ⟨_, _, h⟩ := bind_success _ _ _ h
          obtain ⟨badPair, hbadPair, h⟩ := bind_success _ _ _ h
          cases badPair with
          | true => simp only [↓reduceIte] at h; cases h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨unit1, hmark1, h⟩ := bind_success _ _ _ h
            cases unit1
            obtain ⟨rdot, hdot, h⟩ := bind_success _ _ _ h
            cases rdot with
            | Err err =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at h
              cases h
            | Ok actual =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
              obtain ⟨_, _, h⟩ := bind_success _ _ _ h
              obtain ⟨_, _, h⟩ := bind_success _ _ _ h
              cases hn : (a.next != 22#usize) with
              | true => simp only [hn, ↓reduceIte] at h; cases h
              | false =>
                simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
                obtain ⟨badDot, hbadDot, h⟩ := bind_success _ _ _ h
                cases badDot with
                | true => simp only [↓reduceIte] at h; cases h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  obtain ⟨unit2, hmark2, h⟩ := bind_success _ _ _ h
                  cases unit2
                  exact ⟨alpha0, claim1, alpha1, claim2, w, sliced, pair, actual,
                    ha0, hr0, ha1, hr1, hwgt, hsliced, hpair, hbadPair, hmark1, hdot,
                    rfl, hbadDot, hmark2⟩
#print axioms s2_success_calls
end AspisR1FinishRelationCurrent.FinishCandidateOuterSuccess
