import PV_B3P_SubPanicEvents578227
namespace PV_B3P_SubPanicFamily578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_SubPanicEvents578227
set_option autoImplicit false
/-- All two captured incoming source-event families; no guard input. -/
def sourceState (_caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize) : Bool :=
  !panicEvent zeroSized checks encodedEnd

theorem family_guard (caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize) :
    sourceState caller zeroSized checks encodedEnd = true := panic_guard zeroSized checks encodedEnd

theorem family_certificate {α : Type} (caller : Fin 2) (zeroSized checks : Bool) (encodedEnd : Usize)
    (normal first second : Result α) :
    ¬ diagnostic (sourceState caller zeroSized checks encodedEnd = true) ∧
      branch (sourceState caller zeroSized checks encodedEnd = true) normal first =
        branch (sourceState caller zeroSized checks encodedEnd = true) normal second :=
  panic_certificate zeroSized checks encodedEnd normal first second
#print axioms family_guard
#print axioms family_certificate
end PV_B3P_SubPanicFamily578227
