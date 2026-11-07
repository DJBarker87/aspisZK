import NND_Carrier
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std Result AdapterRw

def account (x : r1_pool_adapter.owned.OwnedAccount) : RSL.OwnedAccount :=
 ⟨key x.key, key x.owner, x.is_signer, x.is_writable, x.executable,
  reply (fun n : Usize => n.val) x.length, reply bytes x.bytes⟩
def accounts (xs : Slice r1_pool_adapter.owned.OwnedAccount) : List RSL.OwnedAccount :=
 xs.val.map account

def outer {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div

/-- Exact getter transport including every ProgramError payload. Clone has
its standard value semantics; no snapshot-specific two-error restriction. -/
theorem getter (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 outer (reply bytes)
  (r1_pool_adapter.owned.OwnedAccount.data {ops with op35 := fun e => ok e} a) =
 ok ((account a).data) := by
 cases h : a.bytes <;> simp [r1_pool_adapter.owned.OwnedAccount.data,outer,reply,account,RSL.OwnedAccount.data,h]

theorem accounts_length (xs : Slice r1_pool_adapter.owned.OwnedAccount) :
 (accounts xs).length = xs.val.length := by simp [accounts]

theorem account_fields (a : r1_pool_adapter.owned.OwnedAccount) :
 (account a).key = key a.key ∧ (account a).owner = key a.owner ∧
 (account a).is_signer = a.is_signer ∧ (account a).is_writable = a.is_writable ∧
 (account a).executable = a.executable ∧ (account a).bytes = reply bytes a.bytes :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms getter
#print axioms accounts_length
#print axioms account_fields
end NND_Carrier
