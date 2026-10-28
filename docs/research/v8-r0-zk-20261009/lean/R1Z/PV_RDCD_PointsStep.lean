import R1Z.PV_CB_Op118Funs
import R1Z.PV_RDCD_Range194
set_option autoImplicit false
namespace R1Z.PV_RDCD_PointsStep
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_ShippedOp118.aspis_core.field.QM31
abbrev Iter := core.iter.adapters.rev.Rev PV_RDCD_Range194.Range
/-- Exact deployed step, preserving the array write and both continuation fields. -/
def source (z : Array Q 10#usize) (iter : Iter) (successor : Array Q 10#usize) (carry : Q) := do
  let next ← PV_RDCD_Range194.backward iter.iter
  match next.1 with
  | none => ok (ControlFlow.done successor)
  | some coordinate =>
    let bit ← Array.index_usize z coordinate
    let bit_and_carry ← PV_CB_ShippedOp118.aspis_core.field.QM31.mul bit carry
    let q ← PV_CB_ShippedOp118.aspis_core.field.QM31.add bit carry
    let q1 ← PV_CB_ShippedOp118.aspis_core.field.QM31.add bit_and_carry bit_and_carry
    let q2 ← PV_CB_ShippedOp118.aspis_core.field.QM31.sub q q1
    let successor1 ← Array.update successor coordinate q2
    ok (ControlFlow.cont ((⟨next.2⟩ : Iter), successor1, bit_and_carry))
/-- No mutable-borrow restoration is discarded; all Results, including errors/divergence, remain. -/
theorem emitted (z : Array Q 10#usize) (iter : Iter) (successor : Array Q 10#usize) (carry : Q) :
    PV_CB_ShippedOp118.aspis_core.state_only_prefix.state_only_statement_points_loop.body z iter successor carry = source z iter successor carry := by
  unfold PV_CB_ShippedOp118.aspis_core.state_only_prefix.state_only_statement_points_loop.body source
  rw [PV_RDCD_Range194.reverse_dispatch]
  cases h : PV_RDCD_Range194.backward iter.iter with
  | fail e => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨o,it⟩; rfl
#print axioms emitted
end R1Z.PV_RDCD_PointsStep
