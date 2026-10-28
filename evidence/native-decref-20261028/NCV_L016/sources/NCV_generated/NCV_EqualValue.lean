import NCV_EqualRun
set_option autoImplicit false
namespace NCV_EqualValue
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem same_iff (b v : Slice U8) (length : b.val.length=v.val.length) :
    NCV_EqualRun.SameFrom b v 0 ↔ b.val=v.val := by
  constructor
  · intro h
    apply List.ext_getElem
    · exact length
    · intro i hb hv
      have e := h i (Nat.zero_le i) hb
      simpa only [NCV_ZeroStep.byte,List.getElem?_eq_getElem hb,
        List.getElem?_eq_getElem hv,Option.getD_some] using e
  · intro h i _ _
    simp only [NCV_ZeroStep.byte,h]

theorem value (b v : Slice U8) (cap : b.val.length ≤ 768) :
    NCV_Reference.equal b v=ok (decide (b.val=v.val)) := by
  classical
  by_cases length : b.val.length=v.val.length
  · have h : (Slice.len b != Slice.len v)=false := by scalar_tac
    unfold NCV_Reference.equal
    rw [h]
    simp only [Bool.false_eq_true,ite_false]
    rw [NCV_EqualRun.run b v 0#usize cap length (by scalar_tac)]
    rw [show (0#usize).val=0 from rfl, propext (same_iff b v length)]
    by_cases same : b.val=v.val <;> simp only [same,ite_true,ite_false,bind_tc_ok,decide_true,decide_false]
  · have h : (Slice.len b != Slice.len v)=true := by scalar_tac
    have no : b.val≠v.val := by intro e;exact length (congrArg List.length e)
    unfold NCV_Reference.equal
    rw [h]
    simp only [ite_true,decide_false,no,Bool.true_eq_true]

#print axioms same_iff
#print axioms value
end NCV_EqualValue
