import S9TwoCallScalarMeaningV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9AfterScalarTermSumsV1

open AspisR1S9HelperP6

local instance concreteOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize

/-- Exact selected generated body suffix after the three source-ordered sums.
This isolates the branch without changing any operation, argument, or effect. -/
def afterSums [AspisR1S9HelperP6.FieldOps]
    (ap1 : W) (side : U) (iterNext : core.ops.range.Range U)
    (weights0 : W) (low first2 first3 all : field.WideExact)
    (q4 q16 : Q) : Result (ControlFlow (core.ops.range.Range U × W) W) :=
  if side = 0#usize then do
    let we4 ← field.WideExact.mul low all
    let weights1 ← Array.update weights0 0#usize we4
    let we5 ← field.WideExact.mul low first3
    let we6 ← field.WideExact.mul_qm31 we5 q16
    let a ← Array.update weights1 1#usize we6
    ok (cont (iterNext, a))
  else do
    let we4 ← Array.index_usize weights0 1#usize
    let i ← Array.index_usize weights.PERM 3#usize
    let we5 ← Array.index_usize ap1 i
    let we6 ← field.WideExact.mul_m31 we5 weights.QUARTER
    let we7 ← field.WideExact.mul low we6
    let we8 ← field.WideExact.add we4 we7
    let weights1 ← Array.update weights0 1#usize we8
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

/-- Invert the complete post-scalar body. The result retains the exact
generated four-term `from_fn`, all source-ordered reads and additions, and the
same complete side-specific suffix result. -/
theorem after_scalar_success_terms_and_sums
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (q4 q8 q12 q16 : Q) (low : field.WideExact)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (htail : @AspisR1S9TwoCallScalarMeaningV2.afterScalar
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low = .ok flow) :
    ∃ (terms : Array field.WideExact (4#usize))
      (state : (W × Array Q (4#usize)) × U)
      (we we1 first2 we2 first3 we3 all : field.WideExact),
      @core.array.from_fn field.WideExact weights.factored_s2_libra_weights.closure
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
        weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (ap1, Array.make 4#usize [field.QM31.ONE,q4,q8,q12]) = .ok (terms,state) ∧
      Array.index_usize terms 0#usize = .ok we ∧
      Array.index_usize terms 1#usize = .ok we1 ∧
      @field.WideExact.add concreteOps we we1 = .ok first2 ∧
      Array.index_usize terms 2#usize = .ok we2 ∧
      @field.WideExact.add concreteOps first2 we2 = .ok first3 ∧
      Array.index_usize terms 3#usize = .ok we3 ∧
      @field.WideExact.add concreteOps first3 we3 = .ok all ∧
      @afterSums
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        ap1 side iterNext weights0 low first2 first3 all q4 q16 = .ok flow := by
  have h := htail
  unfold AspisR1S9TwoCallScalarMeaningV2.afterScalar at h
  rcases bind_success_inv
      (@core.array.from_fn field.WideExact weights.factored_s2_libra_weights.closure
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
        weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (ap1, Array.make 4#usize [field.QM31.ONE,q4,q8,q12])) _ _ h with
    ⟨result,hfromfn,h⟩
  rcases result with ⟨terms,state⟩
  rcases bind_success_inv (Array.index_usize terms 0#usize) _ _ h with
    ⟨we,hwe,h⟩
  rcases bind_success_inv (Array.index_usize terms 1#usize) _ _ h with
    ⟨we1,hwe1,h⟩
  rcases bind_success_inv (@field.WideExact.add concreteOps we we1) _ _ h with
    ⟨first2,hadd2,h⟩
  rcases bind_success_inv (Array.index_usize terms 2#usize) _ _ h with
    ⟨we2,hwe2,h⟩
  rcases bind_success_inv (@field.WideExact.add concreteOps first2 we2) _ _ h with
    ⟨first3,hadd3,h⟩
  rcases bind_success_inv (Array.index_usize terms 3#usize) _ _ h with
    ⟨we3,hwe3,h⟩
  rcases bind_success_inv (@field.WideExact.add concreteOps first3 we3) _ _ h with
    ⟨all,haddAll,h⟩
  change @afterSums AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    ap1 side iterNext weights0 low first2 first3 all q4 q16 = .ok flow at h
  exact ⟨terms,state,we,we1,first2,we2,first3,we3,all,
    hfromfn,hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,h⟩

#print axioms after_scalar_success_terms_and_sums

end AspisR1S9AfterScalarTermSumsV1
