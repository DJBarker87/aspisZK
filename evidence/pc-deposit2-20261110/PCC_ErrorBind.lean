import PCC_ErrorTransport
set_option autoImplicit false
namespace PCC
/-- Propagation through ? is congruent for the exact ABI quotient, retaining
Result tag; successful continuations must separately be related. -/
theorem abi_related_bind {α β : Type} (x y : Except ProgramError α)
    (f g : α → Except ProgramError β) (h : AbiRelated x y)
    (continuation : ∀ a, AbiRelated (f a) (g a)) :
    AbiRelated (x.bind f) (y.bind g) := by
  cases x with
  | ok a => cases y with
    | ok b => change a = b at h; subst b; exact continuation a
    | error e => exact False.elim h
  | error e => cases y with
    | ok b => exact False.elim h
    | error f => exact h
#print axioms abi_related_bind
end PCC
