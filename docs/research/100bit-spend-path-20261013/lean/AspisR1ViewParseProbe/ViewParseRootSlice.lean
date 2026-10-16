import AspisR1ViewParseProbe.ParseSuccessRound1Index
import AspisR1ViewParseProbe.ParseShapeRound1Root

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1ViewParseProbe.ViewParseRootSlice

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem branch_continue_inv {α E : Type}
    (r : core.result.Result α E) (a : α)
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue a)) :
    r = .Ok a := by
  cases r with
  | Ok x => simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch] at h

/-- A successful two-fold parse takes the root-present parser branch, and stores the
fixed-width root array in the returned view. -/
theorem successful_parse_exposes_root_source_slice
    (query_checks : Slice Std.U8 → transport.Variant →
      Result (core.result.Result Unit verifier.Error))
    (input : Slice Std.U8) (view : verifier.View)
    (hparse : verifier.View.parse_with_query_checks query_checks input =
      ok (core.result.Result.Ok view))
    (hfold : transport.Variant.folds view.variant = ok 2#usize) :
    ∃ rootArray rootStart endRoot rootSlice tryResult,
      view.folded_root = some rootArray ∧
      (rootStart + 32#usize : Result Std.Usize) = ok endRoot ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
        { start := rootStart, «end» := endRoot } = ok rootSlice ∧
      core.array.TryFromSharedArraySlice.try_from 32#usize rootSlice = ok tryResult ∧
      core.result.Result.map_err
        verifier.View.parse.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError
        tryResult () = ok (core.result.Result.Ok rootArray) ∧
      (∃ shape, verifier.View.parse_shape input = ok (.Ok shape) ∧
        shape.folded_root_start = some rootStart) := by
  obtain ⟨shape, hshape, hindex, hvariant⟩ :=
    (AspisR1ViewParseProbe.ParseSuccessRound1Index.parse_success_round1_index
      query_checks input view hparse hfold).2
  obtain ⟨rootStart, hrootStart, _hwidth⟩ :=
    AspisR1ViewParseProbe.ParseShapeRound1Root.parse_shape_round1_root
      input shape hshape (by simpa [hvariant] using hfold)
  unfold verifier.View.parse_with_query_checks at hparse
  obtain ⟨parsedShape, hparsedShape, hrest⟩ := bind_success _ _ _ hparse
  have hparsed : parsedShape = core.result.Result.Ok shape := by
    exact Result.ok.inj (hparsedShape.symm.trans hshape)
  rw [hparsed] at hrest
  obtain ⟨flow, hflow, hrest⟩ := bind_success _ _ _ hrest
  have hflow' : flow = core.ops.control_flow.ControlFlow.Continue shape := by
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using hflow.symm
  subst flow
  simp only [bind_tc_ok] at hrest
  rw [hrootStart] at hrest
  obtain ⟨endRoot, hendRoot, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨rootSlice, hrootSlice, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨rootArrayResult, hrootArrayResult, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨mappedRoot, hmappedRoot, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨rootFlow, hrootFlow, hrest⟩ := bind_success _ _ _ hrest
  cases rootFlow with
  | Break residual =>
      cases residual with
      | Ok impossible => cases impossible
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hrest
  | Continue rootArray =>
    have hrootArrayResult' : mappedRoot = core.result.Result.Ok rootArray := by
      exact branch_continue_inv mappedRoot rootArray hrootFlow
    obtain ⟨semantic, hsemantic, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨y1, hy1, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨round0, hround0, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨round1, hround1, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨finalMessage, hfinalMessage, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨queryBytes, hqueryBytes, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨r3, hr3, hrest⟩ := bind_success _ _ _ hrest
    obtain ⟨cf2, hcf2, hrest⟩ := bind_success _ _ _ hrest
    cases cf2 with
    | Break residual =>
        cases residual with
        | Ok impossible => cases impossible
        | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at hrest
    | Continue _ =>
      obtain ⟨r4, hr4, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨cf3, hcf3, hrest⟩ := bind_success _ _ _ hrest
      cases cf3 with
      | Break residual =>
          cases residual with
          | Ok impossible => cases impossible
          | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at hrest
      | Continue _ =>
        obtain ⟨folds, hfolds, hrest⟩ := bind_success _ _ _ hrest
        have hfolds2 : folds = 2#usize := by
          have hfv : transport.Variant.folds shape.variant = ok 2#usize := by
            simpa [hvariant] using hfold
          exact Result.ok.inj (hfolds.symm.trans hfv)
        rw [hfolds2] at hrest
        simp only [if_true] at hrest
        obtain ⟨r5, hr5, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨cf4, hcf4, hrest⟩ := bind_success _ _ _ hrest
        cases cf4 with
        | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at hrest
        | Continue _ =>
          obtain ⟨r6, hr6, hrest⟩ := bind_success _ _ _ hrest
          obtain ⟨cf5, hcf5, hrest⟩ := bind_success _ _ _ hrest
          cases cf5 with
          | Break residual =>
              cases residual with
              | Ok impossible => cases impossible
              | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at hrest
          | Continue _ =>
            obtain ⟨r7, hr7, hrest⟩ := bind_success _ _ _ hrest
            obtain ⟨cf6, hcf6, hrest⟩ := bind_success _ _ _ hrest
            cases cf6 with
            | Break residual =>
                cases residual with
                | Ok impossible => cases impossible
                | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at hrest
            | Continue _ =>
              simp only [bind_tc_ok] at hrest
              have hinner := Result.ok.inj hrest
              have hfield : (some rootArray : Option (Array Std.U8 32#usize)) = view.folded_root := by
                injection hinner with hrecord
                exact congrArg (fun x : verifier.View => x.folded_root) hrecord
              have hmap :
                  core.result.Result.map_err
                    verifier.View.parse.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError
                    rootArrayResult () = ok (core.result.Result.Ok rootArray) := by
                rw [hrootArrayResult'] at hmappedRoot
                exact hmappedRoot
              exact ⟨rootArray, rootStart, endRoot, rootSlice, rootArrayResult,
                hfield.symm, hendRoot, hrootSlice, hrootArrayResult, hmap,
                ⟨shape, hshape, hrootStart⟩⟩

#print axioms successful_parse_exposes_root_source_slice

end AspisR1ViewParseProbe.ViewParseRootSlice
