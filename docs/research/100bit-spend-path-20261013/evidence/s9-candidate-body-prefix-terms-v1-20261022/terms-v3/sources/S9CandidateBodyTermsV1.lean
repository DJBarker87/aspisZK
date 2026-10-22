import S9CandidateBodyPrefixV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateBodyTermsV1

open AspisR1S9CandidateBodyPrefixV1
open AspisR1S9CandidateHelperV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31

def candidateHigh (q41 q8 q12 : Q) : Array Q (4#usize) :=
  Array.make 4#usize [field.QM31.ONE,q41,q8,q12]

def candidateTerms (t0 t1 t2 t3 : field.WideExact) : W :=
  Array.make 4#usize [t0,t1,t2,t3]

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Per-term child calls from the candidate generated body. Every field is an
exact Result equation for a call in the body, not a semantic value premise. -/
structure CandidateTermCall (ap1 : W) (high : Array Q (4#usize)) (i : U) where
  perm : U
  input : field.WideExact
  coefficient : Q
  product : field.WideExact
  term : field.WideExact
  permRead : Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM i = .ok perm
  inputRead : Array.index_usize ap1 perm = .ok input
  coefficientRead : Array.index_usize high i = .ok coefficient
  wideMulCall : field.WideExact.mul_qm31 input coefficient = .ok product
  scalarMulCall : field.WideExact.mul_m31 product
    _root_.AspisR1S9CandidateHelperV1.weights.QUARTER = .ok term

/-- Exact continuation after the explicit four-term array is built. -/
def candidateAfterTerms
    (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : field.WideExact) (perm3 : U)
    (t0 t1 t2 t3 : field.WideExact) :
    Result (ControlFlow (R × W) W) := do
  let we8 ← Array.index_usize (candidateTerms t0 t1 t2 t3) 0#usize
  let we9 ← Array.index_usize (candidateTerms t0 t1 t2 t3) 1#usize
  let first2 ← field.WideExact.add we8 we9
  let we10 ← Array.index_usize (candidateTerms t0 t1 t2 t3) 2#usize
  let first3 ← field.WideExact.add first2 we10
  let we11 ← Array.index_usize (candidateTerms t0 t1 t2 t3) 3#usize
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
    let we13 ← Array.index_usize ap1 perm3
    let we14 ← field.WideExact.mul_m31 we13
      _root_.AspisR1S9CandidateHelperV1.weights.QUARTER
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

/-- Invert the exact post-scalar continuation. The explicit term array and
all four child-call records are obtained from the same continuation returned
by `candidate_active_prefix_from_success`; the remaining exact tail is kept. -/
theorem candidate_after_low_terms_from_success
    (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : field.WideExact)
    (flow : ControlFlow (R × W) W)
    (hrest : candidateAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow) :
    ∃ (c0 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 0#usize)
      (c1 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 1#usize)
      (c2 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 2#usize)
      (c3 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 3#usize),
      candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
        c3.perm c0.term c1.term c2.term c3.term = .ok flow := by
  have hcur := hrest
  unfold candidateAfterLow at hcur
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 0#usize)
    _ _ hcur with ⟨i0,hi0,hcur⟩
  rcases bind_success_inv
    (Array.index_usize ap1 i0) _ _ hcur with ⟨x0,hx0,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (candidateHigh q41 q8 q12) 0#usize) _ _ hcur with
      ⟨a0,ha0,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_qm31 x0 a0) _ _ hcur with ⟨m0,hm0,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m0 _root_.AspisR1S9CandidateHelperV1.weights.QUARTER)
    _ _ hcur with ⟨t0,ht0,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 1#usize)
    _ _ hcur with ⟨i1,hi1,hcur⟩
  rcases bind_success_inv
    (Array.index_usize ap1 i1) _ _ hcur with ⟨x1,hx1,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (candidateHigh q41 q8 q12) 1#usize) _ _ hcur with
      ⟨a1,ha1,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_qm31 x1 a1) _ _ hcur with ⟨m1,hm1,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m1 _root_.AspisR1S9CandidateHelperV1.weights.QUARTER)
    _ _ hcur with ⟨t1,ht1,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 2#usize)
    _ _ hcur with ⟨i2,hi2,hcur⟩
  rcases bind_success_inv
    (Array.index_usize ap1 i2) _ _ hcur with ⟨x2,hx2,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (candidateHigh q41 q8 q12) 2#usize) _ _ hcur with
      ⟨a2,ha2,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_qm31 x2 a2) _ _ hcur with ⟨m2,hm2,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m2 _root_.AspisR1S9CandidateHelperV1.weights.QUARTER)
    _ _ hcur with ⟨t2,ht2,hcur⟩
  rcases bind_success_inv
    (Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize)
    _ _ hcur with ⟨i3,hi3,hcur⟩
  rcases bind_success_inv
    (Array.index_usize ap1 i3) _ _ hcur with ⟨x3,hx3,hcur⟩
  rcases bind_success_inv
    (Array.index_usize (candidateHigh q41 q8 q12) 3#usize) _ _ hcur with
      ⟨a3,ha3,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_qm31 x3 a3) _ _ hcur with ⟨m3,hm3,hcur⟩
  rcases bind_success_inv
    (field.WideExact.mul_m31 m3 _root_.AspisR1S9CandidateHelperV1.weights.QUARTER)
    _ _ hcur with ⟨t3,ht3,hcur⟩
  change candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
    i3 t0 t1 t2 t3 = .ok flow at hcur
  exact ⟨⟨i0,x0,a0,m0,t0,hi0,hx0,ha0,hm0,ht0⟩,
    ⟨i1,x1,a1,m1,t1,hi1,hx1,ha1,hm1,ht1⟩,
    ⟨i2,x2,a2,m2,t2,hi2,hx2,ha2,hm2,ht2⟩,
    ⟨i3,x3,a3,m3,t3,hi3,hx3,ha3,hm3,ht3⟩,hcur⟩

#print axioms candidate_after_low_terms_from_success

end AspisR1S9CandidateBodyTermsV1
