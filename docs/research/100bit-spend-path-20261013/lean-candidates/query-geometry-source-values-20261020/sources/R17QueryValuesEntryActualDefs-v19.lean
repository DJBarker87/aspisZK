import R17QueryPerItemValuesV2
import R17QueryIndexArithmeticV6

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17QueryValuesEntryActualV1

open AspisR1QueryGeometryActual
open R17QueryPerItemValuesV2

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

inductive QueryValuesError where
  | Query
  | IndexOutOfRange
  deriving DecidableEq

/-- Executable semantics of the emitted `map_err` followed by `?` and
`FromResidual` sequence. A failing error callback remains a failing/diverging
outer Result; an inner error is propagated unchanged after mapping. -/
def sourceMapTryFromResidual {α β : Type}
    (f : QueryValuesError → Result QueryValuesError)
    (r : core.result.Result α QueryValuesError)
    (k : α → Result (core.result.Result β QueryValuesError)) :
    Result (core.result.Result β QueryValuesError) := do
  let mapped ←
    match r with
    | core.result.Result.Ok a => pure (core.result.Result.Ok a)
    | core.result.Result.Err e => do
        let e' ← f e
        pure (core.result.Result.Err e')
  match mapped with
  | core.result.Result.Ok a => k a
  | core.result.Result.Err e => pure (core.result.Result.Err e)

/-- Direct match form used in the source-cut helper. -/
def sourceDirectMatch {α β : Type}
    (f : QueryValuesError → Result QueryValuesError)
    (r : core.result.Result α QueryValuesError)
    (k : α → Result (core.result.Result β QueryValuesError)) :
    Result (core.result.Result β QueryValuesError) :=
  match r with
  | core.result.Result.Ok a => k a
  | core.result.Result.Err e => do
      let e' ← f e
      pure (core.result.Result.Err e')

theorem sourceMapTryFromResidual_eq_directMatch {α β : Type}
    (f : QueryValuesError → Result QueryValuesError)
    (r : core.result.Result α QueryValuesError)
    (k : α → Result (core.result.Result β QueryValuesError)) :
    sourceMapTryFromResidual f r k = sourceDirectMatch f r k := by
  cases r with
  | Ok a => rfl
  | Err e =>
      cases hf : f e <;> simp [sourceMapTryFromResidual, sourceDirectMatch, hf]

theorem queryErrorBranch_matches_emitted_closure {α β : Type}
    (r : core.result.Result α QueryValuesError)
    (k : α → Result (core.result.Result β QueryValuesError)) :
    sourceDirectMatch (fun _ => pure QueryValuesError.Query) r k =
      (match r with
       | core.result.Result.Ok a => k a
       | core.result.Result.Err _ => pure (core.result.Result.Err QueryValuesError.Query)) := by
  cases r <;> rfl

/-- Exact successful branch of the extracted FibreIndex constructor, with
the concrete error payload abstracted so no external template is imported. -/
def fibreIndexNew (i : Std.Usize) :
    Result (core.result.Result domain.FibreIndex QueryValuesError) := do
  if i < 262144#usize then
    pure (.Ok i)
  else
    pure (.Err .IndexOutOfRange)

/-- Source-cut adapter for `verifier.query_values_entry`. The body follows the
emitted call order; only map_err/FromResidual are expressed as direct matches,
the error payload is abstracted, and Iterator.any is an explicit argument. -/
def queryValuesEntry (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    Result (core.result.Result ((Array field.M31 5#usize) × field.M31) QueryValuesError) := do
  let u ← lift (UScalar.cast .Usize q)
  let r ← fibreIndexNew u
  match r with
  | .Err _ => pure (.Err .Query)
  | .Ok val =>
    let point ← fast_domain.fibre_point actualCMOps val
    let i ← UScalar.div u (4#usize)
    let i1 ← UScalar.mul i (4#usize)
    let r2 ← fibreIndexNew i1
    match r2 with
    | .Err _ => pure (.Err .Query)
    | .Ok val1 =>
      let line_x ← R17FibrePointLineNodeActual.line_node actualCMOps actualM31Ops val1
      let i2 ← UScalar.mul i (4#usize)
      let i3 ← UScalar.add i2 (3#usize)
      let r4 ← fibreIndexNew i3
      match r4 with
      | .Err _ => pure (.Err .Query)
      | .Ok val2 =>
        let line_y ← R17FibrePointLineNodeActual.line_node actualCMOps actualM31Ops val2
        let m ← actualM31Ops.mul line_x line_x
        let m1 ← actualM31Ops.double m
        let line_z ← actualM31Ops.sub m1 (1#u32)
        let s ← lift (Array.to_slice
          (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z]))
        let it ← core.slice.Slice.iter s
        let (b, _) ← anyCheck it
        if b then pure (.Err .Query)
        else pure (.Ok (Array.make 5#usize
          [point.x, point.y, line_x, line_y, line_z], line_z))

theorem fibreIndexNew_success {i : Std.Usize}
    (hi : i.val < 262144) :
    fibreIndexNew i = .ok (.Ok i) := by
  simp [fibreIndexNew, UScalar.lt_equiv, hi]
  rfl

theorem fibreIndexNew_success_inv {i j : Std.Usize}
    (h : fibreIndexNew i = .ok (.Ok j)) :
    j = i ∧ i.val < 262144 := by
  unfold fibreIndexNew at h
  simp only [UScalar.lt_equiv] at h
  split at h
  · have hval : i = j := by
      change ok (core.result.Result.Ok i) = ok (core.result.Result.Ok j) at h
      cases Result.ok.inj h
      rfl
    exact ⟨hval.symm, by assumption⟩
  · have hval : core.result.Result.Err QueryValuesError.IndexOutOfRange = core.result.Result.Ok j :=
      Result.ok.inj h
    cases hval

theorem successful_queryValuesEntry_indices
    (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (line_z : field.M31)
    (h : queryValuesEntry q anyCheck = .ok (.Ok (arr, line_z))) :
    ∃ (u ix iy : Std.Usize),
      lift (UScalar.cast UScalarTy.Usize q) = .ok u ∧
      u.val < 262144 ∧
      ix.val = (u.val / 4) * 4 ∧
      iy.val = (u.val / 4) * 4 + 3 ∧
      ix.val < 262144 ∧ iy.val < 262144 := by
  unfold queryValuesEntry at h
  rcases bind_ok_inv h with ⟨u, hcast, hrest0⟩
  rcases bind_ok_inv hrest0 with ⟨r0, hr0, hmatch0⟩
  cases r0 with
  | Err e =>
    change ok (core.result.Result.Err QueryValuesError.Query) =
      ok (core.result.Result.Ok (arr, line_z)) at hmatch0
    cases Result.ok.inj hmatch0
  | Ok val =>
    obtain ⟨hval0, hu⟩ := fibreIndexNew_success_inv hr0
    rcases bind_ok_inv hmatch0 with ⟨point, hpoint, hrest1⟩
    rcases bind_ok_inv hrest1 with ⟨i, hdiv, hrest2⟩
    rcases bind_ok_inv hrest2 with ⟨i1, hmul1, hrest3⟩
    rcases bind_ok_inv hrest3 with ⟨r1, hr1, hmatch1⟩
    cases r1 with
    | Err e =>
      change ok (core.result.Result.Err QueryValuesError.Query) =
        ok (core.result.Result.Ok (arr, line_z)) at hmatch1
      cases Result.ok.inj hmatch1
    | Ok val1 =>
      obtain ⟨hval1, hi1⟩ := fibreIndexNew_success_inv hr1
      rcases bind_ok_inv hmatch1 with ⟨line_x, hlineX, hrest4⟩
      rcases bind_ok_inv hrest4 with ⟨i2, hmul2, hrest5⟩
      rcases bind_ok_inv hrest5 with ⟨i3, hadd, hrest6⟩
      rcases bind_ok_inv hrest6 with ⟨r2, hr2, hmatch2⟩
      cases r2 with
      | Err e =>
        change ok (core.result.Result.Err QueryValuesError.Query) =
          ok (core.result.Result.Ok (arr, line_z)) at hmatch2
        cases Result.ok.inj hmatch2
      | Ok val2 =>
        obtain ⟨hval2, hi2⟩ := fibreIndexNew_success_inv hr2
        have hi12 : i1 = i2 := Result.ok.inj (hmul1.symm.trans hmul2)
        have hadd' := hadd
        rw [← hi12] at hadd'
        have hc : R17QueryIndexArithmeticV1.checkedLineIndices u = .ok (i1, i3) := by
          unfold R17QueryIndexArithmeticV1.checkedLineIndices
          simp [hdiv, hmul1, hadd']
          rfl
        obtain ⟨hix, hiy, hixb, hiyb⟩ :=
          R17QueryIndexArithmeticV1.successful_checkedLineIndices u i1 i3 hu hc
        exact ⟨u, i1, i3, hcast, hu, hix, hiy, hixb, hiyb⟩

theorem successful_queryValuesEntry_core
    (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (line_z : field.M31)
    (h : queryValuesEntry q anyCheck = .ok (.Ok (arr, line_z))) :
    ∃ u ix iy point line_x line_y,
      u.val < 262144 ∧ ix.val < 262144 ∧ iy.val < 262144 ∧
      ix.val = (u.val / 4) * 4 ∧ iy.val = (u.val / 4) * 4 + 3 ∧
      perQueryCore actualCMOps actualM31Ops u ix iy =
        .ok (point, line_x, line_y, line_z) ∧
      arr = Array.make 5#usize [point.x, point.y, line_x, line_y, line_z] ∧
      ∃ it it', anyCheck it = .ok (false, it') := by
  unfold queryValuesEntry at h
  rcases bind_ok_inv h with ⟨u, hcast, hrest0⟩
  rcases bind_ok_inv hrest0 with ⟨r0, hr0, hmatch0⟩
  cases r0 with
  | Err e =>
    change ok (core.result.Result.Err QueryValuesError.Query) =
      ok (core.result.Result.Ok (arr, line_z)) at hmatch0
    cases Result.ok.inj hmatch0
  | Ok val =>
    obtain ⟨hval0, hu⟩ := fibreIndexNew_success_inv hr0
    rcases bind_ok_inv hmatch0 with ⟨point, hpoint, hrest1⟩
    rcases bind_ok_inv hrest1 with ⟨i, hdiv, hrest2⟩
    rcases bind_ok_inv hrest2 with ⟨i1, hmul1, hrest3⟩
    rcases bind_ok_inv hrest3 with ⟨r1, hr1, hmatch1⟩
    cases r1 with
    | Err e =>
      change ok (core.result.Result.Err QueryValuesError.Query) =
        ok (core.result.Result.Ok (arr, line_z)) at hmatch1
      cases Result.ok.inj hmatch1
    | Ok val1 =>
      obtain ⟨hval1, hi1⟩ := fibreIndexNew_success_inv hr1
      rcases bind_ok_inv hmatch1 with ⟨line_x, hlineX, hrest4⟩
      rcases bind_ok_inv hrest4 with ⟨i2, hmul2, hrest5⟩
      rcases bind_ok_inv hrest5 with ⟨i3, hadd, hrest6⟩
      rcases bind_ok_inv hrest6 with ⟨r2, hr2, hmatch2⟩
      cases r2 with
      | Err e =>
        change ok (core.result.Result.Err QueryValuesError.Query) =
          ok (core.result.Result.Ok (arr, line_z)) at hmatch2
        cases Result.ok.inj hmatch2
      | Ok val2 =>
        obtain ⟨hval2, hi2⟩ := fibreIndexNew_success_inv hr2
        rcases bind_ok_inv hmatch2 with ⟨line_y, hlineY, hrest7⟩
        rcases bind_ok_inv hrest7 with ⟨m, hm, hrest8⟩
        rcases bind_ok_inv hrest8 with ⟨m1, hm1, hrest9⟩
        rcases bind_ok_inv hrest9 with ⟨line_z0, hsub, hrest10⟩
        rcases bind_ok_inv hrest10 with ⟨s, hs, hrest11⟩
        rcases bind_ok_inv hrest11 with ⟨it, hit, hrest12⟩
        rcases bind_ok_inv hrest12 with ⟨bi, hany, hif⟩
        rcases bi with ⟨b, it'⟩
        cases b with
        | true =>
          change ok (core.result.Result.Err QueryValuesError.Query) =
            ok (core.result.Result.Ok (arr, line_z)) at hif
          cases Result.ok.inj hif
        | false =>
          have hret : (Array.make 5#usize
              [point.x, point.y, line_x, line_y, line_z0], line_z0) =
              (arr, line_z) := by
            change ok (core.result.Result.Ok
                (Array.make 5#usize
                  [point.x, point.y, line_x, line_y, line_z0], line_z0)) =
              ok (core.result.Result.Ok (arr, line_z)) at hif
            exact core.result.Result.Ok.inj (Result.ok.inj hif)
          have harr : arr = Array.make 5#usize
              [point.x, point.y, line_x, line_y, line_z0] :=
            congrArg Prod.fst hret |>.symm
          have hz : line_z0 = line_z := congrArg Prod.snd hret
          have hi12 : i1 = i2 := Result.ok.inj (hmul1.symm.trans hmul2)
          have hadd' := hadd
          rw [← hi12] at hadd'
          have hc : R17QueryIndexArithmeticV1.checkedLineIndices u = .ok (i1, i3) := by
            unfold R17QueryIndexArithmeticV1.checkedLineIndices
            simp [hdiv, hmul1, hadd']
            change Bind.bind (ok i3) (fun y => pure (i1, y)) = ok (i1, i3)
            rfl
          obtain ⟨hix, hiy, _, _⟩ :=
            R17QueryIndexArithmeticV1.successful_checkedLineIndices u i1 i3 hu hc
          have hix' : val1.val = (u.val / 4) * 4 := by rw [hval1, hix]
          have hiy' : val2.val = (u.val / 4) * 4 + 3 := by rw [hval2, hiy]
          have hpoint' : fast_domain.fibre_point actualCMOps u = .ok point := by
            simpa [hval0] using hpoint
          have hlineX' : R17FibrePointLineNodeActual.line_node
              actualCMOps actualM31Ops val1 = .ok line_x := hlineX
          have hlineY' : R17FibrePointLineNodeActual.line_node
              actualCMOps actualM31Ops val2 = .ok line_y := hlineY
          have hcore : perQueryCore actualCMOps actualM31Ops u val1 val2 =
              .ok (point, line_x, line_y, line_z) := by
            unfold perQueryCore
            simp [hpoint', hlineX', hlineY', hm, hm1, hsub, hz]
            rfl
          have hval1bound : val1.val < 262144 := by rw [hval1]; exact hi1
          have hval2bound : val2.val < 262144 := by rw [hval2]; exact hi2
          exact ⟨u, val1, val2, point, line_x, line_y, hu, hval1bound, hval2bound,
            hix', hiy', hcore, by simpa [hz] using harr, it, it', hany⟩

#print axioms queryValuesEntry
#print axioms fibreIndexNew_success
#print axioms fibreIndexNew_success_inv
#print axioms successful_queryValuesEntry_indices
#print axioms successful_queryValuesEntry_core
#print axioms sourceMapTryFromResidual_eq_directMatch
#print axioms queryErrorBranch_matches_emitted_closure
end R17QueryValuesEntryActualV1
