import NGG_Compare
import NGG_Loader
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_Metadata
abbrev Key := NGG_Compare.Key
def loader (owner a b c : Key) : Bool := decide (owner.val=a.val ∨ owner.val=b.val ∨ owner.val=c.val)
theorem verifier (account : NGG_Ref.Account) (selected a b c : Key) :
    NGG_Ref.verifier account selected (NGG_Loader.loaders a b c) =
      ok (if account.key.val ≠ selected.val ∨ account.executable = false ∨ account.signer = true ∨ account.writable = true ∨ loader account.owner a b c = false
        then .Err NGG_Ref.Error.InvalidVerifierProgram else .Ok ()) := by
  simp only [NGG_Ref.verifier,NGG_Compare.ne,NGG_Loader.result,bind_tc_ok]
  cases he : account.executable <;> cases hs : account.signer <;> cases hw : account.writable <;>
    by_cases hk : account.key.val = selected.val <;>
    by_cases hl : account.owner.val=a.val ∨ account.owner.val=b.val ∨ account.owner.val=c.val <;>
    simp [he,hs,hw,hk,hl,loader]
#print axioms verifier
theorem token (account : NGG_Ref.Account) (token_id a b c : Key) :
    NGG_Ref.token account token_id (NGG_Loader.loaders a b c) =
      ok (if account.key.val ≠ token_id.val ∨ account.executable = false ∨ account.signer = true ∨ account.writable = true ∨ loader account.owner a b c = false
        then .Err NGG_Ref.Error.InvalidTokenProgram else .Ok ()) := by
  simp only [NGG_Ref.token,NGG_Compare.ne,NGG_Loader.result,bind_tc_ok]
  cases he : account.executable <;> cases hs : account.signer <;> cases hw : account.writable <;>
    by_cases hk : account.key.val = token_id.val <;>
    by_cases hl : account.owner.val=a.val ∨ account.owner.val=b.val ∨ account.owner.val=c.val <;>
    simp [he,hs,hw,hk,hl,loader]
#print axioms token
end NGG_Metadata
