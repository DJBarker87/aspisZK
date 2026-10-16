import AspisR1ViewParseProbe.CleanParameterizedParse

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ViewParseProbe.ParseSuccessRound1Index

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem branch_continue_inv {α E : Type}
    (r : core.result.Result α E) (a : α)
    (h : core.result.Result.Insts.CoreOpsTry.branch r =
      ok (.Continue a)) : r = .Ok a := by
  cases r with
  | Ok x => simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch] at h

/-- Successful candidate View parsing, for any query-check implementation,
forces the returned folded round1 slice through the source echeck call. -/
theorem parse_success_round1_index
    (query_checks : Slice Std.U8 → transport.Variant → Result (core.result.Result Unit verifier.Error))
    (bytes : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks bytes =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    verifier.echeck view.round1 false = ok (core.result.Result.Ok ()) ∧
      ∃ shape,
        verifier.View.parse_shape bytes = ok (core.result.Result.Ok shape) ∧
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := shape.round1_start, «end» := shape.round1_end } =
          ok view.round1 ∧ shape.variant = view.variant := by
  unfold verifier.View.parse_with_query_checks at hparse
  obtain ⟨parsedShape, hshape, hrest⟩ := bind_success _ _ _ hparse
  cases parsedShape with
  | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at hrest
      have hin : core.result.Result.Err e = core.result.Result.Ok view :=
        Result.ok.inj hrest
      cases hin
  | Ok shape =>
      obtain ⟨flow, hflow, hrest⟩ := bind_success _ _ _ hrest
      have hflow' : flow = core.ops.control_flow.ControlFlow.Continue shape := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using hflow.symm
      subst flow
      simp only [bind_tc_ok] at hrest
      cases hroot : shape.folded_root_start with
      | none =>
        rw [hroot] at hrest
        obtain ⟨s, hs, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s1, hs1, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s2, hs2, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s3, hs3, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s4, hs4, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s5, hs5, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨r1, hr1, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨cf1, hcf1, hrest⟩ := bind_success _ _ _ hrest
        cases cf1 with
        | Continue u =>
          have hr1' : r1 = core.result.Result.Ok u := by
            exact branch_continue_inv r1 u hcf1
          obtain ⟨r2, hr2, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨cf2, hcf2, hrest⟩ := bind_success _ _ _ hrest
          cases cf2 with
          | Continue u2 =>
            have hr2' : r2 = core.result.Result.Ok u2 := by
              exact branch_continue_inv r2 u2 hcf2
            obtain ⟨i, hi, hrest⟩ := bind_success _ _ _ hrest
            by_cases hguard : i = 2#usize
            · simp only [hguard, if_pos] at hrest
              obtain ⟨r3, hr3, hrest⟩ := bind_success _ _ _ hrest
              obtain ⟨cf3, hcf3, hrest⟩ := bind_success _ _ _ hrest
              cases cf3 with
              | Continue u3 =>
                have hr3' : r3 = core.result.Result.Ok u3 := by
                  exact branch_continue_inv r3 u3 hcf3
                obtain ⟨r4, hr4, hrest⟩ := bind_success _ _ _ hrest
                obtain ⟨cf4, hcf4, hrest⟩ := bind_success _ _ _ hrest
                cases cf4 with
                | Continue u4 =>
                  have hr4' : r4 = core.result.Result.Ok u4 := by
                    exact branch_continue_inv r4 u4 hcf4
                  obtain ⟨r5, hr5, hrest⟩ := bind_success _ _ _ hrest
                  obtain ⟨cf5, hcf5, hrest⟩ := bind_success _ _ _ hrest
                  cases cf5 with
                  | Continue u5 =>
                    have hr5' : r5 = core.result.Result.Ok u5 := by
                      exact branch_continue_inv r5 u5 hcf5
                    simp only [bind_tc_ok] at hrest
                    have hinner :
                        (core.result.Result.Ok
                          { variant := shape.variant, semantic := s, y1 := s1,
                            inactive := shape.inactive, round0 := s2, folded_root := none,
                            round1 := s3, final_message := s4, query_bytes := s5 } :
                            core.result.Result verifier.View verifier.Error) =
                        (core.result.Result.Ok view :
                            core.result.Result verifier.View verifier.Error) := by
                      exact Result.ok.inj hrest
                    injection hinner with hview
                    have hround : view.round1 = s3 := by
                      cases hview
                      rfl
                    have hvariantOut : shape.variant = view.variant := by
                      cases hview
                      rfl
                    rw [hround]
                    have hu3 : u3 = () := Subsingleton.elim _ _
                    constructor
                    · simpa [hr3', hu3] using hr3
                    · refine ⟨shape, ?_, ?_, ?_⟩
                      · exact hshape
                      · simpa [hround] using hs3
                      · exact hvariantOut
                  | Break residual =>
                    cases residual with
                    | Ok impossible => cases impossible
                    | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at hrest
                | Break residual =>
                  cases residual with
                  | Ok impossible => cases impossible
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at hrest
              | Break residual =>
                cases residual with
                | Ok impossible => cases impossible
                | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at hrest
            · simp only [hguard, if_neg] at hrest
              obtain ⟨r3, hr3, hrest⟩ := bind_success _ _ _ hrest
              obtain ⟨cf3, hcf3, hrest⟩ := bind_success _ _ _ hrest
              cases cf3 with
              | Continue u3 =>
                have hr3' : r3 = core.result.Result.Ok u3 := by
                  exact branch_continue_inv r3 u3 hcf3
                obtain ⟨r4, hr4, hrest⟩ := bind_success _ _ _ hrest
                obtain ⟨cf4, hcf4, hrest⟩ := bind_success _ _ _ hrest
                cases cf4 with
                | Continue u4 =>
                  have hr4' : r4 = core.result.Result.Ok u4 := by
                    exact branch_continue_inv r4 u4 hcf4
                  simp only [bind_tc_ok] at hrest
                  have hinner :
                      (core.result.Result.Ok
                        { variant := shape.variant, semantic := s, y1 := s1,
                          inactive := shape.inactive, round0 := s2, folded_root := none,
                          round1 := s3, final_message := s4, query_bytes := s5 } :
                          core.result.Result verifier.View verifier.Error) =
                      (core.result.Result.Ok view :
                          core.result.Result verifier.View verifier.Error) := by
                    exact Result.ok.inj hrest
                  injection hinner with hview
                  have hvariant : view.variant = shape.variant := by
                    cases hview
                    rfl
                  have hi' : transport.Variant.folds shape.variant = ok i := hi
                  have hfold' : transport.Variant.folds shape.variant = ok 2#usize := by
                    simpa [hvariant] using hfold
                  have : i = 2#usize := by
                    have heq := hi'.symm.trans hfold'
                    injection heq
                  exact (hguard this).elim
                | Break residual =>
                  cases residual with
                  | Ok impossible => cases impossible
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at hrest
              | Break residual =>
                cases residual with
                | Ok impossible => cases impossible
                | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at hrest
          | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hrest
        | Break residual =>
          cases residual with
          | Ok impossible => cases impossible
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hrest
      | some start =>
        rw [hroot] at hrest
        obtain ⟨i0, hi0, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨s0, hs0, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨r1, hr1, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨r2, hr2, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨cf1, hcf1, hrest⟩ := bind_success _ _ _ hrest
        cases cf1 with
        | Continue rootVal =>
          have hr2' : r2 = core.result.Result.Ok rootVal := by
            exact branch_continue_inv r2 rootVal hcf1
          obtain ⟨s1, hs1, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨s2, hs2, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨s3, hs3, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨s4, hs4, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨s5, hs5, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨s6, hs6, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨r3, hr3, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨cf2, hcf2, hrest⟩ := bind_success _ _ _ hrest
          cases cf2 with
          | Continue u2 =>
            have hr3' : r3 = core.result.Result.Ok u2 := by
              exact branch_continue_inv r3 u2 hcf2
            obtain ⟨r4, hr4, hrest⟩ := bind_success _ _ _ hrest
            obtain ⟨cf3, hcf3, hrest⟩ := bind_success _ _ _ hrest
            cases cf3 with
            | Continue u3 =>
              have hr4' : r4 = core.result.Result.Ok u3 := by
                exact branch_continue_inv r4 u3 hcf3
              obtain ⟨i, hi, hrest⟩ := bind_success _ _ _ hrest
              by_cases hguard : i = 2#usize
              · simp only [hguard, if_pos] at hrest
                obtain ⟨r5, hr5, hrest⟩ := bind_success _ _ _ hrest
                obtain ⟨cf4, hcf4, hrest⟩ := bind_success _ _ _ hrest
                cases cf4 with
                | Continue u4 =>
                  have hr5' : r5 = core.result.Result.Ok u4 := by
                    exact branch_continue_inv r5 u4 hcf4
                  obtain ⟨r6, hr6, hrest⟩ := bind_success _ _ _ hrest
                  obtain ⟨cf5, hcf5, hrest⟩ := bind_success _ _ _ hrest
                  cases cf5 with
                  | Continue u5 =>
                    have hr6' : r6 = core.result.Result.Ok u5 := by
                      exact branch_continue_inv r6 u5 hcf5
                    obtain ⟨r7, hr7, hrest⟩ := bind_success _ _ _ hrest
                    obtain ⟨cf6, hcf6, hrest⟩ := bind_success _ _ _ hrest
                    cases cf6 with
                    | Continue u6 =>
                      have hr7' : r7 = core.result.Result.Ok u6 := by
                        exact branch_continue_inv r7 u6 hcf6
                      simp only [bind_tc_ok] at hrest
                      have hinner :
                          (core.result.Result.Ok
                            { variant := shape.variant, semantic := s1, y1 := s2,
                              inactive := shape.inactive, round0 := s3,
                              folded_root := some rootVal, round1 := s4,
                              final_message := s5, query_bytes := s6 } :
                              core.result.Result verifier.View verifier.Error) =
                          (core.result.Result.Ok view :
                              core.result.Result verifier.View verifier.Error) := by
                        exact Result.ok.inj hrest
                      injection hinner with hview
                      have hround : view.round1 = s4 := by
                        cases hview
                        rfl
                      have hvariantOut : shape.variant = view.variant := by
                        cases hview
                        rfl
                      rw [hround]
                      have hu4 : u4 = () := Subsingleton.elim _ _
                      constructor
                      · simpa [hr5', hu4] using hr5
                      · refine ⟨shape, ?_, ?_, ?_⟩
                        · exact hshape
                        · simpa [hround] using hs4
                        · exact hvariantOut
                    | Break residual =>
                      cases residual with
                      | Ok impossible => cases impossible
                      | Err e =>
                        simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                          core.convert.FromSame.from] at hrest
                  | Break residual =>
                    cases residual with
                    | Ok impossible => cases impossible
                    | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at hrest
                | Break residual =>
                  cases residual with
                  | Ok impossible => cases impossible
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at hrest
              · simp only [hguard, if_neg] at hrest
                obtain ⟨r5, hr5, hrest⟩ := bind_success _ _ _ hrest
                obtain ⟨cf4, hcf4, hrest⟩ := bind_success _ _ _ hrest
                cases cf4 with
                | Continue u4 =>
                  have hr5' : r5 = core.result.Result.Ok u4 := by
                    exact branch_continue_inv r5 u4 hcf4
                  obtain ⟨r6, hr6, hrest⟩ := bind_success _ _ _ hrest
                  obtain ⟨cf5, hcf5, hrest⟩ := bind_success _ _ _ hrest
                  cases cf5 with
                  | Continue u5 =>
                    have hr6' : r6 = core.result.Result.Ok u5 := by
                      exact branch_continue_inv r6 u5 hcf5
                    simp only [bind_tc_ok] at hrest
                    have hinner :
                      (core.result.Result.Ok
                        { variant := shape.variant, semantic := s1, y1 := s2,
                          inactive := shape.inactive, round0 := s3,
                          folded_root := some rootVal, round1 := s4,
                          final_message := s5, query_bytes := s6 } :
                          core.result.Result verifier.View verifier.Error) =
                      (core.result.Result.Ok view :
                          core.result.Result verifier.View verifier.Error) := by
                      exact Result.ok.inj hrest
                    injection hinner with hview
                    have hvariant : view.variant = shape.variant := by
                      cases hview
                      rfl
                    have hi' : transport.Variant.folds shape.variant = ok i := hi
                    have hfold' : transport.Variant.folds shape.variant = ok 2#usize := by
                      simpa [hvariant] using hfold
                    have : i = 2#usize := by
                      have heq := hi'.symm.trans hfold'
                      injection heq
                    exact (hguard this).elim
                  | Break residual =>
                    cases residual with
                    | Ok impossible => cases impossible
                    | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at hrest
                | Break residual =>
                  cases residual with
                  | Ok impossible => cases impossible
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from] at hrest
            | Break residual =>
              cases residual with
              | Ok impossible => cases impossible
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrest
          | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hrest
        | Break residual =>
          cases residual with
          | Ok impossible => cases impossible
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hrest

#print axioms parse_success_round1_index

end AspisR1ViewParseProbe.ParseSuccessRound1Index
