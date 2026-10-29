import Aeneas

/-! Small owned control references. Source bindings are recorded separately;
these are value/Result laws and do not claim observer or binary refinement. -/
namespace R1Z.PV_RDCD3_Control194
set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-- Blanket IntoIterator for an Iterator returns the entire state unchanged. -/
def intoIter {I : Type} (i : I) : I := i

theorem intoIter_state {I : Type} (i : I) : intoIter i = i := rfl

/-- Reached Result::unwrap's success path does not call Debug or the panic
formatter. The native error branch projects to the existing Result panic. -/
def unwrap {T E : Type} : Except E T → Result T
  | .ok t => ok t
  | .error _ => fail .panic

theorem unwrap_ok {T E : Type} (t : T) : unwrap (Except.ok (ε := E) t) = ok t := rfl

theorem unwrap_error {T E : Type} (e : E) :
    unwrap (Except.error (α := T) e) = fail .panic := rfl

/-- An earlier checked-read error prevents both unwrap branches. -/
theorem prior_failure {T U : Type} (e : Error) (f : T → Result U) :
    (fail e >>= f) = fail e := rfl

/-- Neither identity conversion allocates or performs a memory copy. -/
def fromIdentity {T : Type} (t : T) : T := t

def intoIdentity {T : Type} (t : T) : T := fromIdentity t

theorem into_from {T : Type} (t : T) : intoIdentity t = t := rfl

/-- At the retained Result interface, a panic never invokes its continuation.
Its external diagnostics remain outside this source-value interface. -/
theorem panic_terminal {T U : Type} (f : T → Result U) :
    (fail .panic >>= f) = fail .panic := rfl

#print axioms intoIter_state
#print axioms unwrap_ok
#print axioms unwrap_error
#print axioms prior_failure
#print axioms into_from
#print axioms panic_terminal
end R1Z.PV_RDCD3_Control194
