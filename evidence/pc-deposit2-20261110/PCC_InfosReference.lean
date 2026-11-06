import PCC_BasicReferences
set_option autoImplicit false
namespace PCC
open PCA
/-- Full exact_five_accounts checks (including duplicate keys) precede clones.
The vector stores SAME admitted account identities in source,mint,vault,
authority,token order. Rc/handle association is PCC-NativeView. -/
def infosReference (accounts : List Nat) : Reference (Vector Nat 5) := fun s =>
  match accounts with
  | [mint,source,authority,vault,token] =>
    let keys := accounts.map (fun a => (s.loans.state.accounts a).key)
    if keys.Pairwise (· ≠ ·) then
      ⟨s,[],.ok ⟨#[source,mint,vault,authority,token],rfl⟩⟩
    else ⟨s,[],.error (.program 0x41532015)⟩
  | _ => ⟨s,[],.error (.program (if accounts.length < 5 then notEnoughKeys else 2*2^32))⟩

def RowSpec_POOL_382 (native : List Nat → Reference (Vector Nat 5)) : Prop :=
  Reference.RowSpec (fun args s => ∀ a ∈ args, a < s.accountCount) native infosReference
end PCC
