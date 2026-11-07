import LIB_Carriers
import NJH_Observer
set_option autoImplicit false
namespace LIB_Observer
open Aeneas Aeneas.Std
abbrev value : RSL.Observer := none
/-- The existing CLOSED emitted body, with no function-pointer Kani credit. -/
theorem emitted (ops : AdapterRw.Ops) : AdapterRw.observer ops = .ok none :=
  AspisR1.NJH_Observer.emitted ops
/-- Both canonical and emitted observer choices have the deployed None arm. -/
theorem canonical : value = none := rfl
#print axioms emitted
#print axioms canonical
end LIB_Observer
