import S2G_InstalledValues
import S2G_Copy
import S2E_Types

/-! Concrete PURE reference value instance for five S2E fields. Seven callbacks
remain explicit and unproved. This construction is not a native verified stub:
identity on a ghost state here is a definition, never a native frame theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2G.Children
open S2E_Reference.S2E_Reference

/-- Lift a pure computation into a value-only reference with an inert ghost.
Use a separately proved effect port for any native state instantiation. -/
def liftValue {A S : Type} (state : S) (value : Result A) : Result (A × S) := do
  let a ← value
  ok (a,state)

def installValues {C S : Type} (remaining : Children C S)
    (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops) : Children C S :=
  { remaining with
    decode := fun state bytes => liftValue state (S2G.decode ops vops bytes)
    validate := fun state statement => liftValue state (S2G.validate statement)
    candidate := fun state afterstate => liftValue state (S2G.candidate afterstate)
    first := fun state statement publicInput proof split =>
      liftValue state (S2G.first ops vops statement publicInput proof split)
    copy := fun state sdk slot bytes => do
      let after ← S2G.Copy.copy sdk slot bytes
      ok (state,after) }

theorem liftValue_success {A S : Type} (state after : S) (value : Result A) (a : A)
    (h : liftValue state value = ok (a,after)) : value = ok a ∧ after = state := by
  cases value with
  | fail e => cases h
  | div => cases h
  | ok b => cases h; exact ⟨rfl,rfl⟩

theorem decoder_contract {C S : Type} (remaining : Children C S)
    (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (state after : S) (bytes : Slice U8) (statement : S2G.Statement)
    (h : (installValues remaining ops vops).decode state bytes = ok (.Ok statement,after)) :
    bytes.val.length = 1880 ∧ S2G.validate statement = ok (.Ok ()) := by
  have value := (liftValue_success state after _ _ h).1
  exact ⟨(S2G.decode_contract ops vops bytes statement value).1,
    (S2G.decode_contract ops vops bytes statement value).2.1⟩

/-- Unfilled fields are preserved literally, not supplied as proved children. -/
theorem unresolved_fields {C S : Type} (remaining : Children C S)
    (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops) :
    (installValues remaining ops vops).second = remaining.second ∧
    (installValues remaining ops vops).validate_asq8 = remaining.validate_asq8 ∧
    (installValues remaining ops vops).«public» = remaining.«public» ∧
    (installValues remaining ops vops).emit = remaining.emit ∧
    (installValues remaining ops vops).clear_return_data = remaining.clear_return_data ∧
    (installValues remaining ops vops).drop_checkpoint = remaining.drop_checkpoint ∧
    (installValues remaining ops vops).drop_statement = remaining.drop_statement :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms liftValue_success
#print axioms decoder_contract
#print axioms unresolved_fields
end AspisR1.S2G.Children
