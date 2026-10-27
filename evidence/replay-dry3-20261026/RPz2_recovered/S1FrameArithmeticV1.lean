import Aeneas
set_option autoImplicit false
namespace AspisS1FrameArithmetic
open Aeneas Aeneas.Std Result

/-- Accepted checked operations supply their exact natural values without an
independent no-overflow premise. These are the actual typed Std operations. -/
theorem add_value {ty : UScalarTy} (a b c : UScalar ty) (success : a+b=ok c) :
    c.val=a.val+b.val := by
  have facts := UScalar.add_equiv a b
  rw [success] at facts
  exact facts.2.1

theorem mul_value {ty : UScalarTy} (a b c : UScalar ty) (success : a*b=ok c) :
    c.val=a.val*b.val := by
  have facts := UScalar.mul_equiv a b
  change UScalar.mul a b=ok c at success
  rw [success] at facts
  exact facts.2.1

/-- TOTAL typed multiplication whenever the exact result has a valid carrier.
The supplied equality itself forces the arithmetic range bound. -/
theorem mul_exact {ty : UScalarTy} (a b c : UScalar ty) (value : c.val=a.val*b.val) :
    a*b=ok c := by
  obtain ⟨z,call,exactValue⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x:=a) (y:=b) (by scalar_tac))
  have equal : z=c := by scalar_tac
  simpa only [equal] using call

#print axioms add_value
#print axioms mul_value
#print axioms mul_exact
end AspisS1FrameArithmetic
