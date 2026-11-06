import PCC_ProgramError
set_option autoImplicit false
namespace PCC
/-- Dispatcher preserves full error value and inspects only the Result tag.
The Bool records its set_return_data(&[]) occurrence, not a runtime value. -/
def dispatchReturn (reply : Except ProgramError Unit) :
    Except ProgramError Unit × Bool := (reply, match reply with | .ok _ => false | .error _ => true)

theorem dispatch_error (e : ProgramError) :
    dispatchReturn (.error e) = (.error e, true) := rfl

theorem abi_related_dispatch (x y : Except ProgramError Unit)
    (h : AbiRelated x y) :
    entrypoint (dispatchReturn x).1 = entrypoint (dispatchReturn y).1 ∧
    (dispatchReturn x).2 = (dispatchReturn y).2 := by
  cases x with
  | ok a => cases y with
    | ok b => cases a; cases b; exact ⟨rfl,rfl⟩
    | error f => exact False.elim h
  | error e => cases y with
    | ok b => exact False.elim h
    | error f => exact ⟨h,rfl⟩

/-- A constant map never inspects its input payload. Raw errors may have
separate carriers (deposit/forest/leaf); the map remains constant. -/
def constantMap {Raw α : Type} (e : ProgramError) :
    Except Raw α → Except ProgramError α
  | .ok value => .ok value
  | .error _ => .error e

theorem constant_map_error {Raw α : Type} (e : ProgramError) (raw : Raw) :
    constantMap (α := α) e (.error raw) = .error e := rfl

#print axioms dispatch_error
#print axioms abi_related_dispatch
#print axioms constant_map_error
end PCC
