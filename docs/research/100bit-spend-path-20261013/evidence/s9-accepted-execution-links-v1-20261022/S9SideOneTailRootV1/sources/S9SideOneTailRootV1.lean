import S9TwoCallScalarMeaningV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S9SideOneTailRootV1

local instance selectedOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array AspisR1S9HelperP6.field.WideExact (4#usize)
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev Ops := AspisR1S9HelperP6.FieldOps

/-- The selected source suffix for side one, copied from the `else` branch of
the active S9 helper body. It includes every read, arithmetic call, update,
and the final array returned by this suffix; the enclosing `.cont` is outside
this definition. -/
def sideOneTail (old ap1 : W) (low all first2 : S) (q4 q16 : Q) : Result W := by
  letI : Ops := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  exact do
    let we4 ← Array.index_usize old 1#usize
    let i ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
    let we5 ← Array.index_usize ap1 i
    let we6 ← AspisR1S9HelperP6.field.WideExact.mul_m31 we5
      _root_.AspisR1S9HelperP6.weights.QUARTER
    let we7 ← AspisR1S9HelperP6.field.WideExact.mul low we6
    let we8 ← AspisR1S9HelperP6.field.WideExact.add we4 we7
    let weights1 ← Array.update old 1#usize we8
    let we9 ← AspisR1S9HelperP6.field.WideExact.mul low all
    let we10 ← AspisR1S9HelperP6.field.WideExact.mul_qm31 we9 q4
    let weights2 ← Array.update weights1 2#usize we10
    let we11 ← AspisR1S9HelperP6.field.WideExact.mul low first2
    let q3 ← AspisR1S9HelperP6.field.QM31.mul q16 q4
    let we12 ← AspisR1S9HelperP6.field.WideExact.mul_qm31 we11 q3
    let out ← Array.update weights2 3#usize we12
    ok out

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Successful side-one suffix execution exposes the exact ordered child calls
and array updates in the selected source body. This is control-flow evidence;
it makes no arithmetic-result or S9 output claim. -/
theorem sideOneTail_success_children
    (old ap1 : W) (low all first2 : S) (q4 q16 : Q) (out : W)
    (h : sideOneTail old ap1 low all first2 q4 q16 = .ok out) :
    ∃ (we4 : S) (i : U) (we5 we6 we7 we8 : S) (weights1 : W)
      (we9 we10 : S) (weights2 : W) (we11 : S) (q3 : Q) (we12 : S),
      Array.index_usize old 1#usize = .ok we4 ∧
      Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize = .ok i ∧
      Array.index_usize ap1 i = .ok we5 ∧
      AspisR1S9HelperP6.field.WideExact.mul_m31 we5
        _root_.AspisR1S9HelperP6.weights.QUARTER = .ok we6 ∧
      AspisR1S9HelperP6.field.WideExact.mul low we6 = .ok we7 ∧
      AspisR1S9HelperP6.field.WideExact.add we4 we7 = .ok we8 ∧
      Array.update old 1#usize we8 = .ok weights1 ∧
      AspisR1S9HelperP6.field.WideExact.mul low all = .ok we9 ∧
      AspisR1S9HelperP6.field.WideExact.mul_qm31 we9 q4 = .ok we10 ∧
      Array.update weights1 2#usize we10 = .ok weights2 ∧
      AspisR1S9HelperP6.field.WideExact.mul low first2 = .ok we11 ∧
      AspisR1S9HelperP6.field.QM31.mul q16 q4 = .ok q3 ∧
      AspisR1S9HelperP6.field.WideExact.mul_qm31 we11 q3 = .ok we12 ∧
      Array.update weights2 3#usize we12 = .ok out := by
  letI : Ops := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  unfold sideOneTail at h
  rcases bind_success_inv (Array.index_usize old 1#usize) _ _ h with
    ⟨we4, hwe4, h⟩
  rcases bind_success_inv
      (Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize) _ _ h with
    ⟨i, hi, h⟩
  rcases bind_success_inv (Array.index_usize ap1 i) _ _ h with
    ⟨we5, hwe5, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul_m31 we5
        _root_.AspisR1S9HelperP6.weights.QUARTER) _ _ h with
    ⟨we6, hwe6, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul low we6) _ _ h with
    ⟨we7, hwe7, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.add we4 we7) _ _ h with
    ⟨we8, hwe8, h⟩
  rcases bind_success_inv (Array.update old 1#usize we8) _ _ h with
    ⟨weights1, hw1, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul low all) _ _ h with
    ⟨we9, hwe9, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul_qm31 we9 q4) _ _ h with
    ⟨we10, hwe10, h⟩
  rcases bind_success_inv (Array.update weights1 2#usize we10) _ _ h with
    ⟨weights2, hw2, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul low first2) _ _ h with
    ⟨we11, hwe11, h⟩
  rcases bind_success_inv (AspisR1S9HelperP6.field.QM31.mul q16 q4) _ _ h with
    ⟨q3, hq3, h⟩
  rcases bind_success_inv
      (AspisR1S9HelperP6.field.WideExact.mul_qm31 we11 q3) _ _ h with
    ⟨we12, hwe12, h⟩
  rcases bind_success_inv (Array.update weights2 3#usize we12) _ _ h with
    ⟨outValue, hout, h⟩
  have houtEq : outValue = out := Result.ok.inj h
  subst out
  exact ⟨we4, i, we5, we6, we7, we8, weights1, we9, we10, weights2,
    we11, q3, we12, hwe4, hi, hwe5, hwe6, hwe7, hwe8, hw1, hwe9,
    hwe10, hw2, hwe11, hq3, hwe12, hout⟩

#print axioms sideOneTail_success_children

end AspisR1.S9SideOneTailRootV1
