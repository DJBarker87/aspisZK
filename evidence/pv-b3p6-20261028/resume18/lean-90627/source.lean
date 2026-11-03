import PV_B3P_SliceEvents578227
namespace PV_B3P_SubPanicEvents578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- The exact scalar projection of the two casts and SubChecked in helper317.
The deployed/source cohort uses the 64-bit usize instantiation. -/
def overflowFlag (left right : Usize) : Bool :=
  (UScalar.overflowing_sub (UScalar.cast .U64 left) (UScalar.cast .U64 right)).2

theorem cast_sub_safe (left right : Usize) (ordered : right.val ≤ left.val) :
    overflowFlag left right = false := by
  have castOrder : ¬(UScalar.cast .U64 left).val < (UScalar.cast .U64 right).val := by
    have leftBound : left.val < UScalar.size .U64 := by scalar_tac
    have rightBound : right.val < UScalar.size .U64 := by scalar_tac
    rw [UScalar.cast_val_eq,UScalar.cast_val_eq,
      Nat.mod_eq_of_lt leftBound,Nat.mod_eq_of_lt rightBound]
    omega
  have spec := UScalar.overflowing_sub_eq (UScalar.cast .U64 left) (UScalar.cast .U64 right)
  simp only [castOrder,if_false] at spec
  exact spec.2

/-- Only the two captured slice-next input events enter helper317. A false
flag means the source's overflow branch never reaches its panic tail. -/
def panicEvent (zeroSized checks : Bool) (encodedEnd : Usize) : Bool :=
  match PV_B3P_SliceEvents578227.sourceEvent zeroSized checks encodedEnd with
  | none => false
  | some _ => overflowFlag encodedEnd 1#usize

theorem panic_absent (zeroSized checks : Bool) (encodedEnd : Usize) :
    panicEvent zeroSized checks encodedEnd = false := by
  cases observed : PV_B3P_SliceEvents578227.sourceEvent zeroSized checks encodedEnd with
  | none => simp only [panicEvent,observed]
  | some state =>
    have nonzero : encodedEnd ≠ 0#usize := by
      intro zero
      subst encodedEnd
      cases zeroSized <;> cases checks <;>
        simp only [PV_B3P_SliceEvents578227.sourceEvent,Bool.false_eq_true,if_false,if_true] at observed
      all_goals cases observed
    have safe := PV_B3P_CounterGuards571227.subtraction_guard encodedEnd nonzero
    simp only [panicEvent,observed]
    apply cast_sub_safe
    exact safe

theorem panic_guard (zeroSized checks : Bool) (encodedEnd : Usize) :
    (!panicEvent zeroSized checks encodedEnd) = true := by
  rw [panic_absent]
  rfl

theorem panic_certificate {α : Type} (zeroSized checks : Bool) (encodedEnd : Usize)
    (normal first second : Result α) :
    ¬ diagnostic ((!panicEvent zeroSized checks encodedEnd) = true) ∧
      branch ((!panicEvent zeroSized checks encodedEnd) = true) normal first =
        branch ((!panicEvent zeroSized checks encodedEnd) = true) normal second :=
  (explicit_panic _ normal first second).2 (panic_guard zeroSized checks encodedEnd)
#print axioms cast_sub_safe
#print axioms panic_absent
#print axioms panic_guard
#print axioms panic_certificate
end PV_B3P_SubPanicEvents578227
