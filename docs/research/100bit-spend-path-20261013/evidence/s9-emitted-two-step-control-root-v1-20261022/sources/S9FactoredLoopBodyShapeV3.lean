import AspisR1S9HelperP6.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9FactoredLoopBodyShapeV3
open AspisR1S9HelperP6

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)

def body [AspisR1S9HelperP6.FieldOps] (ap0 ap1 : W)
    (extra : Array field.QM31 (2#usize)) :
    R × W → Result (ControlFlow (R × W) W) := fun s =>
  weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2

/-- The exact active suffix of the extracted body after its range iterator
returns `some side`. This is copied from the pinned generated Funs body. -/
def activeBody [AspisR1S9HelperP6.FieldOps] (ap0 ap1 : W)
    (extra : Array field.QM31 (2#usize)) (side : U) (iterNext : R)
    (weights : W) : Result (ControlFlow (R × W) W) := do
  let q ← Array.index_usize extra side
  let q1 ← _root_.AspisR1S9HelperP6.weights.kpowers 4#usize q
  let q2 ← Array.index_usize q1 2#usize
  let q4 ← field.QM31.square q2
  let q8 ← field.QM31.square q4
  let q12 ← field.QM31.mul q8 q4
  let q16 ← field.QM31.square q8
  let low ← _root_.AspisR1S9HelperP6.weights.Weights.scalar_factor q1 ap0
  let (terms, _) ←
    core.array.from_fn 4#usize
      _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (ap1, Array.make 4#usize [field.QM31.ONE, q4, q8, q12])
  let we ← Array.index_usize terms 0#usize
  let we1 ← Array.index_usize terms 1#usize
  let first2 ← field.WideExact.add we we1
  let we2 ← Array.index_usize terms 2#usize
  let first3 ← field.WideExact.add first2 we2
  let we3 ← Array.index_usize terms 3#usize
  let all ← field.WideExact.add first3 we3
  if side = 0#usize then do
    let we4 ← field.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we4
    let we5 ← field.WideExact.mul low first3
    let we6 ← field.WideExact.mul_qm31 we5 q16
    let a ← Array.update weights1 1#usize we6
    ok (cont (iterNext, a))
  else do
    let we4 ← Array.index_usize weights 1#usize
    let i ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
    let we5 ← Array.index_usize ap1 i
    let we6 ← field.WideExact.mul_m31 we5 _root_.AspisR1S9HelperP6.weights.QUARTER
    let we7 ← field.WideExact.mul low we6
    let we8 ← field.WideExact.add we4 we7
    let weights1 ← Array.update weights 1#usize we8
    let we9 ← field.WideExact.mul low all
    let we10 ← field.WideExact.mul_qm31 we9 q4
    let weights2 ← Array.update weights1 2#usize we10
    let we11 ← field.WideExact.mul low first2
    let q3 ← field.QM31.mul q16 q4
    let we12 ← field.WideExact.mul_qm31 we11 q3
    let a ← Array.update weights2 3#usize we12
    ok (cont (iterNext, a))

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem body_some_eq_activeBody [AspisR1S9HelperP6.FieldOps]
    (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (iter iterNext : R) (side : U) (weights : W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext)) :
    body ap0 ap1 extra (iter, weights) =
      activeBody ap0 ap1 extra side iterNext weights := by
  unfold body _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop.body
  rw [hnext]
  rfl

theorem active_body_success_is_cont [AspisR1S9HelperP6.FieldOps]
    (ap0 ap1 : W) (extra : Array field.QM31 (2#usize))
    (side : U) (iterNext : R) (weights : W) (flow : ControlFlow (R × W) W)
    (hactive : activeBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ updated, flow = .cont (iterNext, updated) := by
  have hcur := hactive
  unfold activeBody at hcur
  rcases bind_success_inv (Array.index_usize extra side) _ _ hcur with
    ⟨q, hq, hcur⟩
  repeat' (rcases bind_success_inv _ _ _ hcur with ⟨_, _, hcur⟩)
  split at hcur
  all_goals
    repeat' (rcases bind_success_inv _ _ _ hcur with ⟨_, _, hcur⟩)
    cases flow with
    | done final => cases Result.ok.inj hcur
    | cont nextState =>
        have hresult := Result.ok.inj hcur
        cases nextState with
        | mk iter' updated =>
            injection hresult with hpair
            have hiter : iter' = iterNext := congrArg Prod.fst hpair.symm
            refine ⟨updated, ?_⟩
            rw [hiter]

#print axioms active_body_success_is_cont

end AspisR1S9FactoredLoopBodyShapeV3
