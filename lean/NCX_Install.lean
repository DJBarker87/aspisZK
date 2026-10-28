import NCX_Carrier
import NCV_Install
set_option autoImplicit false
noncomputable section
namespace NCX_Install
open Aeneas Aeneas.Std Result

def mapReturn {A B : Type} (f : A → B) : core.result.Result A NCX_Reference.PoolV1VerifierRegistryFormatError →
    core.result.Result B AdapterRw.aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError
  | .Ok a => .Ok (f a)
  | .Err e => .Err (NCX_Carrier.error e)
def op33 (b : Slice U8) := do
  let r ← NCX_Reference.decode_verifier_registry_v2 b
  ok (mapReturn NCX_Carrier.registry r)
def op34 (b : Slice U8) := do
  let r ← NCX_Reference.decode_verifier_registry_entry_v2 b
  ok (mapReturn NCX_Carrier.entry r)
/-- Dictionary selection; native correspondence is a distinct gate. -/
def install (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {base with op33:=op33,op34:=op34}
theorem selected (base : AdapterRw.Ops) :
    (install base).op33=op33 ∧ (install base).op34=op34 := ⟨rfl,rfl⟩
theorem op33_result (b : Slice U8) : op33 b =
    (match NCX_Reference.decode_verifier_registry_v2 b with
      | .ok r => .ok (mapReturn NCX_Carrier.registry r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op33
  cases NCX_Reference.decode_verifier_registry_v2 b <;> rfl
theorem op34_result (b : Slice U8) : op34 b =
    (match NCX_Reference.decode_verifier_registry_entry_v2 b with
      | .ok r => .ok (mapReturn NCX_Carrier.entry r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op34
  cases NCX_Reference.decode_verifier_registry_entry_v2 b <;> rfl
#print axioms selected
#print axioms op33_result
#print axioms op34_result
end NCX_Install
end
