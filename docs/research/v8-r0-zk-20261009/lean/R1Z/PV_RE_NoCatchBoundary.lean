import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
namespace R1Z.PV_RE_NoCatchBoundary
open Aeneas.Std PV_RE_NoCatchCore
/-- A proof-method countermodel, not a claim about extracted/shipped code. -/
def ignored (_ : Result Unit) : Result Unit := .ok ()

theorem result_congruence (a b : Result Unit) : ignored a = ignored b := rfl

/-- Every bind continuation has its local absorption certificate, but this
fact cannot certify an arbitrary surrounding source consumer. -/
theorem local_certificates_insufficient :
    (∀ k : Unit → Result Unit, NoCatch (fun r => r >>= k)) ∧
    ¬ NoCatch ignored := by
  constructor
  · exact fun k => bind_noCatch k
  · intro h
    have bad := h.1 Error.panic
    change Result.ok () = Result.fail Error.panic at bad
    cases bad

#print axioms ignored
#print axioms result_congruence
#print axioms local_certificates_insufficient
end R1Z.PV_RE_NoCatchBoundary
