import AspisR1S9PairCallerStepV1.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9PairCallerBodyPrefixV1

open AspisR1S9PairCallerStepV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31

/-- Exact post-scalar continuation from the generated pair caller loop body.
The operations and order are copied from the pinned generated Funs body; this
definition exists only to name the continuation exposed by bind inversion. -/
def pairAfterLow
    (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : field.WideExact) :
    Result (ControlFlow (R × W) W) := do
  let i ← Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 0#usize
  let we ← Array.index_usize ap1 i
  let q5 ← Array.index_usize (Array.make 4#usize
    [field.QM31.ONE, q41, q8, q12]) 0#usize
  let we1 ← field.WideExact.mul_qm31 we q5
  let term0 ← field.WideExact.mul_m31 we1
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  let i1 ← Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 1#usize
  let we2 ← Array.index_usize ap1 i1
  let q6 ← Array.index_usize (Array.make 4#usize
    [field.QM31.ONE, q41, q8, q12]) 1#usize
  let we3 ← field.WideExact.mul_qm31 we2 q6
  let term1 ← field.WideExact.mul_m31 we3
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  let i2 ← Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 2#usize
  let we4 ← Array.index_usize ap1 i2
  let q7 ← Array.index_usize (Array.make 4#usize
    [field.QM31.ONE, q41, q8, q12]) 2#usize
  let we5 ← field.WideExact.mul_qm31 we4 q7
  let term2 ← field.WideExact.mul_m31 we5
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  let i3 ← Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 3#usize
  let we6 ← Array.index_usize ap1 i3
  let q9 ← Array.index_usize (Array.make 4#usize
    [field.QM31.ONE, q41, q8, q12]) 3#usize
  let we7 ← field.WideExact.mul_qm31 we6 q9
  let term3 ← field.WideExact.mul_m31 we7
    _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
  let we8 ← Array.index_usize (Array.make 4#usize [term0, term1, term2, term3]) 0#usize
  let we9 ← Array.index_usize (Array.make 4#usize [term0, term1, term2, term3]) 1#usize
  let first2 ← field.WideExact.add we8 we9
  let we10 ← Array.index_usize (Array.make 4#usize [term0, term1, term2, term3]) 2#usize
  let first3 ← field.WideExact.add first2 we10
  let we11 ← Array.index_usize (Array.make 4#usize [term0, term1, term2, term3]) 3#usize
  let all ← field.WideExact.add first3 we11
  if side = 0#usize then do
    let we12 ← field.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we12
    let we13 ← field.WideExact.mul low first3
    let we14 ← field.WideExact.mul_qm31 we13 q16
    let a ← Array.update weights1 1#usize we14
    ok (cont (iterNext, a))
  else do
    let we12 ← Array.index_usize weights 1#usize
    let we13 ← Array.index_usize ap1 i3
    let we14 ← field.WideExact.mul_m31 we13
      _root_.AspisR1S9PairCallerStepV1.weights.QUARTER
    let we15 ← field.WideExact.mul low we14
    let we16 ← field.WideExact.add we12 we15
    let weights1 ← Array.update weights 1#usize we16
    let we17 ← field.WideExact.mul low all
    let we18 ← field.WideExact.mul_qm31 we17 q41
    let weights2 ← Array.update weights1 2#usize we18
    let we19 ← field.WideExact.mul low first2
    let q10 ← field.QM31.mul q16 q41
    let we20 ← field.WideExact.mul_qm31 we19 q10
    let a ← Array.update weights2 3#usize we20
    ok (cont (iterNext, a))

/-- The exact active suffix of the pair caller generated body after the range
iterator returns `some side`. -/
def pairActiveBody
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (side : U) (iterNext : R) (weights : W) :
    Result (ControlFlow (R × W) W) := do
  let q ← Array.index_usize extra side
  let q1 ← field.QM31.mul field.QM31.ONE q
  let q2 ← field.QM31.mul q1 q
  let q3 ← field.QM31.mul q2 q
  let unusedQ4 ← field.QM31.mul q3 q
  let q4 ← Array.index_usize
    (Array.make 4#usize [field.QM31.ONE, q1, q2, q3]) 2#usize
  let q41 ← field.QM31.square q4
  let q8 ← field.QM31.square q41
  let q12 ← field.QM31.mul q8 q41
  let q16 ← field.QM31.square q8
  let low ← _root_.AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
    (Array.make 4#usize [field.QM31.ONE, q1, q2, q3]) ap0
  pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The generated parent body selects this exact active suffix on the same
successful `next = some side` result. -/
theorem body_some_eq_pairActiveBody
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter iterNext : R) (side : U) (weights : W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext)) :
    _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights =
        pairActiveBody ap0 ap1 extra side iterNext weights := by
  unfold _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
  rw [hnext]
  rfl

/-- Actual successful pair-caller-body prefix through scalar_factor. All
returned local values are tied to their generated child calls; the final
field is the exact source continuation after the scalar result. -/
theorem pair_active_prefix_from_success
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (side : U) (iterNext : R) (weights : W)
    (flow : ControlFlow (R × W) W)
    (hbody : pairActiveBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : Q)
      (low : field.WideExact),
      Array.index_usize extra side = .ok q ∧
      field.QM31.mul field.QM31.ONE q = .ok q1 ∧
      field.QM31.mul q1 q = .ok q2 ∧
      field.QM31.mul q2 q = .ok q3 ∧
      field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) 2#usize = .ok q4 ∧
      field.QM31.square q4 = .ok q41 ∧
      field.QM31.square q41 = .ok q8 ∧
      field.QM31.mul q8 q41 = .ok q12 ∧
      field.QM31.square q8 = .ok q16 ∧
      _root_.AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
        (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow := by
  have hcur := hbody
  unfold pairActiveBody at hcur
  rcases bind_success_inv (Array.index_usize extra side) _ _ hcur with
    ⟨q,hq,hcur⟩
  rcases bind_success_inv (field.QM31.mul field.QM31.ONE q) _ _ hcur with
    ⟨q1,hq1,hcur⟩
  rcases bind_success_inv (field.QM31.mul q1 q) _ _ hcur with
    ⟨q2,hq2,hcur⟩
  rcases bind_success_inv (field.QM31.mul q2 q) _ _ hcur with
    ⟨q3,hq3,hcur⟩
  rcases bind_success_inv (field.QM31.mul q3 q) _ _ hcur with
    ⟨unusedQ4,hunusedQ4,hcur⟩
  rcases bind_success_inv
      (Array.index_usize (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) 2#usize)
      _ _ hcur with ⟨q4,hq4,hcur⟩
  rcases bind_success_inv (field.QM31.square q4) _ _ hcur with
    ⟨q41,hq41,hcur⟩
  rcases bind_success_inv (field.QM31.square q41) _ _ hcur with
    ⟨q8,hq8,hcur⟩
  rcases bind_success_inv (field.QM31.mul q8 q41) _ _ hcur with
    ⟨q12,hq12,hcur⟩
  rcases bind_success_inv (field.QM31.square q8) _ _ hcur with
    ⟨q16,hq16,hcur⟩
  rcases bind_success_inv
      (_root_.AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
        (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) ap0)
      _ _ hcur with ⟨low,hlow,hcur⟩
  change pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow at hcur
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
    hq,hq1,hq2,hq3,hunusedQ4,hq4,hq41,hq8,hq12,hq16,hlow,hcur⟩

#print axioms body_some_eq_pairActiveBody
#print axioms pair_active_prefix_from_success

end AspisR1S9PairCallerBodyPrefixV1
