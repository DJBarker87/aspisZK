import PV_B3P_SliceEvents578227
namespace PV_B3P_SliceFamily578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SliceEvents578227
set_option autoImplicit false
def sourceState_192 (zeroSized checks : Bool) (encodedEnd : Usize) : Option ArithmeticState :=
  sourceEvent zeroSized checks encodedEnd
theorem certificate_192 {α : Type} (zeroSized checks : Bool) (encodedEnd : Usize)
    (observed : ArithmeticState) (ran : sourceState_192 zeroSized checks encodedEnd = some observed)
    (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  event_certificate zeroSized checks encodedEnd observed ran normal first second
#print axioms certificate_192
def sourceState_237 (zeroSized checks : Bool) (encodedEnd : Usize) : Option ArithmeticState :=
  sourceEvent zeroSized checks encodedEnd
theorem certificate_237 {α : Type} (zeroSized checks : Bool) (encodedEnd : Usize)
    (observed : ArithmeticState) (ran : sourceState_237 zeroSized checks encodedEnd = some observed)
    (normal first second : Result α) :
    ¬ diagnostic (arithmeticGuard observed) ∧
      branch (arithmeticGuard observed) normal first = branch (arithmeticGuard observed) normal second :=
  event_certificate zeroSized checks encodedEnd observed ran normal first second
#print axioms certificate_237
end PV_B3P_SliceFamily578227
