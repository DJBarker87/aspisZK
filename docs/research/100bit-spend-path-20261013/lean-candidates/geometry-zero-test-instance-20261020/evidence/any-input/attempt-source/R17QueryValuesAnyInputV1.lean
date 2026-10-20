import R17QueryPerItemValuesV2
import R17QueryIndexArithmeticV6

open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

namespace R17QueryValuesAnyInputV1
open AspisR1QueryGeometryActual R17QueryPerItemValuesV2

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- A successful query source cut passes `Slice::iter` the same five ordered
values it returns, and the iterator starts at index zero. -/
theorem successful_queryValuesWithAny_input {E : Type}
    (qerror : E) (u ix iy : domain.FibreIndex)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (line_z : field.M31)
    (h : queryValuesWithAny qerror u ix iy anyCheck =
      .ok (.Ok (arr, line_z))) :
    ∃ point line_x line_y iter iter',
      perQueryCore actualCMOps actualM31Ops u ix iy =
        .ok (point, line_x, line_y, line_z) ∧
      arr = Array.make 5#usize [point.x, point.y, line_x, line_y, line_z] ∧
      anyCheck iter = .ok (false, iter') ∧ iter.i = 0 ∧
      iter.slice.val = [point.x, point.y, line_x, line_y, line_z] := by
  unfold queryValuesWithAny at h
  rcases bind_ok_inv h with ⟨point, hpoint, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨line_x, hline_x, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨line_y, hline_y, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨m, hm, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨m1, hm1, hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨line_z0, hline_z, hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨s, hs, hrest7⟩
  rcases bind_ok_inv hrest7 with ⟨iter, hiter, hrest8⟩
  rcases bind_ok_inv hrest8 with ⟨result, hany, hfinal⟩
  rcases result with ⟨b, iter'⟩
  have hb : b = false := by cases b <;> simp_all
  subst b
  have hzero : anyCheck iter = .ok (false, iter') := hany
  change Result.ok (core.result.Result.Ok (Array.make 5#usize
      [point.x, point.y, line_x, line_y, line_z0], line_z0)) =
      .ok (.Ok (arr, line_z)) at hfinal
  have htuple : (Array.make 5#usize
      [point.x, point.y, line_x, line_y, line_z0], line_z0) =
      (arr, line_z) := by
    have hcore : core.result.Result.Ok
        (Array.make 5#usize [point.x, point.y, line_x, line_y, line_z0], line_z0) =
        core.result.Result.Ok (arr, line_z) := Result.ok.inj hfinal
    cases hcore
    rfl
  have harr : Array.make 5#usize
      [point.x, point.y, line_x, line_y, line_z0] = arr := congrArg Prod.fst htuple
  have hline : line_z0 = line_z := congrArg Prod.snd htuple
  subst line_z0
  have hs' : s = Array.to_slice (Array.make 5#usize
      [point.x, point.y, line_x, line_y, line_z]) := by
    have h := hs
    simp [lift] at h
    exact h.symm
  have hsval : s.val = [point.x, point.y, line_x, line_y, line_z] := by
    rw [hs']
    change (Array.make 5#usize
      [point.x, point.y, line_x, line_y, line_z]).val =
      [point.x, point.y, line_x, line_y, line_z]
    rfl
  have hiterEq : iter = (⟨s, 0⟩ : core.slice.iter.Iter field.M31) := by
    have h := hiter
    simp [core.slice.Slice.iter] at h
    exact h.symm
  have hstart : iter.i = 0 := by rw [hiterEq]
  have hinput : iter.slice.val = [point.x, point.y, line_x, line_y, line_z] := by
    rw [hiterEq]
    exact hsval
  refine ⟨point, line_x, line_y, iter, iter', ?_, harr.symm, hzero, hstart, hinput⟩
  simp [perQueryCore, hpoint, hline_x, hline_y, hm, hm1, hline_z, Bind.bind]
  rfl

#print axioms successful_queryValuesWithAny_input
end R17QueryValuesAnyInputV1
