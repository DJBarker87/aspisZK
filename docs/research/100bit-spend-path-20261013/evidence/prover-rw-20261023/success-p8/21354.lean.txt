import R1Z.PV_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_PoleFold
open Aeneas Aeneas.Std Result PV_PoleLeafValue
attribute [local instance] Classical.propDecidable
-- Four ordered native comparisons, with no early exit or omitted operand.
def row (clear active : Bool) (chi : Q) (values : Array (Array Q 2#usize) 2#usize) : Result Bool := do
  let side0 ← Array.index_usize values 0#usize
  let x00 ← Array.index_usize side0 0#usize
  let x01 ← Array.index_usize side0 1#usize
  let side1 ← Array.index_usize values 1#usize
  let x10 ← Array.index_usize side1 0#usize
  let x11 ← Array.index_usize side1 1#usize
  let c0 ← PV_PoleLeafSource.ct_pole.keep_clear clear active chi x00
  let c1 ← PV_PoleLeafSource.ct_pole.keep_clear c0 active chi x01
  let c2 ← PV_PoleLeafSource.ct_pole.keep_clear c1 active chi x10
  PV_PoleLeafSource.ct_pole.keep_clear c2 active chi x11

-- Pointwise Boolean model for a row; source-order effects remain in row above.
def test (active : Bool) (chi : Q) (values : Array (Array Q 2#usize) 2#usize) : Bool :=
  !(active && (chi=PV_ArrayReadValue.get2 (PV_ArrayReadValue.get2 values 0) 0)) &&
  !(active && (chi=PV_ArrayReadValue.get2 (PV_ArrayReadValue.get2 values 0) 1)) &&
  !(active && (chi=PV_ArrayReadValue.get2 (PV_ArrayReadValue.get2 values 1) 0)) &&
  !(active && (chi=PV_ArrayReadValue.get2 (PV_ArrayReadValue.get2 values 1) 1))

theorem row_value (clear active : Bool) (chi : Q)
    (values : Array (Array Q 2#usize) 2#usize) :
    row clear active chi values = ok (clear && test active chi values) := by
  simp only [row,PV_ArrayReadValue.first,PV_ArrayReadValue.second,
    PV_PoleLeafCorrect.keep_clear,bind_tc_ok,test]
  simp only [Bool.and_assoc]
theorem inactive (clear : Bool) (chi : Q)
    (values : Array (Array Q 2#usize) 2#usize) :
    row clear false chi values = ok clear := by
  rw [row_value]
  simp only [test,Bool.false_and,Bool.not_false,Bool.true_and,Bool.and_true]
theorem absorbing (active : Bool) (chi : Q)
    (values : Array (Array Q 2#usize) 2#usize) :
    row false active chi values = ok false := by
  rw [row_value]
  rfl
theorem total (clear active : Bool) (chi : Q)
    (values : Array (Array Q 2#usize) 2#usize) :
    ∃ answer, row clear active chi values = ok answer := ⟨_,row_value clear active chi values⟩
#print axioms total
#print axioms absorbing
#print axioms inactive
#print axioms row_value
end R1Z.PV_PoleFold
