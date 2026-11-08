import PV_LIB_A_TypedDropSource
import PV_LIB_A_Emitted608
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_EmittedDropBinding
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine

/-- Exact emitted glue608 is concrete SpawnHooks, so it needs no generic T
substitution. This source binding is NOT a binder for arbitrary UntrackedDestruct
or an adequacy claim for its still-native nested callees. -/
def programs (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) :
    Option PV_STX2_SliceSyntax.Program :=
  if PV_THR2_OffPath.functionId fn = some 608 then some PV_LIB_A_Emitted608.program else P fn

def fnPtr608 (generics : Data) : Data :=
  .object [("kind",.object [("Fun",.object [("Regular",.number 608)])]),("generics",generics)]

/-- Actual raw FnPtr normalization retains every generic item. -/
theorem exact_program (P : Data → Option PV_STX2_SliceSyntax.Program) (generics : Data) :
    programs P (PV_LIB_A_TypedDropSource.callToken (fnPtr608 generics)) =
      some PV_LIB_A_Emitted608.program := rfl

/-- The body binding is discharged by the exact retained emitted program,
not by a caller assumption that a native destructor leaves the store alone. -/
theorem selected608 (C : Carrier OWNER Data)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) (w : OWNER)
    (wait : PV_STX2_Native.Waiting Data) (generics value : Data) (slot : Nat)
    (completed : c.frame.completed = none) (waiting : c.frame.waiting = some wait)
    (request : wait.request = .drop (fnPtr608 generics) value)
    (action : wait.action = .dropped (.local slot)) :
    PV_LIB_A_TypedDropSource.select C (programs P) c w =
      some ⟨wait,PV_LIB_A_Emitted608.program,⟨c.frame.activation,slot,[]⟩⟩ := by
  simp [PV_LIB_A_TypedDropSource.select,completed,waiting,request,action,
    programs,fnPtr608,PV_LIB_A_TypedDropSource.callToken,PV_THR2_OffPath.functionId,
    PV_STX2_Store.locate]

#print axioms programs
#print axioms fnPtr608
#print axioms exact_program
#print axioms selected608
end PV_LIB_A_EmittedDropBinding
