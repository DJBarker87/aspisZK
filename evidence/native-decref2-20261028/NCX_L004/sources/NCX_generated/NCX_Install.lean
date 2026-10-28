import NCX_Carrier
import NCV_InstallationSupport
set_option autoImplicit false
noncomputable section
namespace NCX_Install
open Aeneas Aeneas.Std Result AspisR1

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
def configure {F E : Type} (missing : DrvC_Installation.Configuration F E) :=
  {NCV_InstallationSupport.configure missing with adapter:=install (NCV_Install.install missing.adapter)}
theorem selected (base : AdapterRw.Ops) :
    (install base).op33=op33 ∧ (install base).op34=op34 := ⟨rfl,rfl⟩
theorem sdk_selected {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op33=op33 ∧
    (DrvC_Installation.sdk (configure missing)).op34=op34 := ⟨rfl,rfl⟩
theorem ncv_retained {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (configure missing).adapter.op48=NCV_Install.op48 ∧
    (configure missing).adapter.op49=NCV_Install.op49 ∧
    (configure missing).adapter.op50=NCV_Install.op50 := ⟨rfl,rfl,rfl⟩
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
#print axioms sdk_selected
#print axioms ncv_retained
#print axioms op33_result
#print axioms op34_result
end NCX_Install
end
