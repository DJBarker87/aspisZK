import Lean
import NHC_NGG_Compare
import NHC_NGG_Loader

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_Metadata
abbrev Key := NHC_NGG_Compare.Key
def loader (owner a b c : Key) : Bool := decide (owner.val=a.val ∨ owner.val=b.val ∨ owner.val=c.val)
theorem verifier (account : NHC_NGG_Ref.Account) (selected a b c : Key) :
    NHC_NGG_Ref.verifier account selected (NHC_NGG_Loader.loaders a b c) =
      ok (if account.key.val ≠ selected.val ∨ account.executable = false ∨ account.signer = true ∨ account.writable = true ∨ loader account.owner a b c = false
        then .Err NHC_NGG_Ref.Error.InvalidVerifierProgram else .Ok ()) := by
  simp only [NHC_NGG_Ref.verifier,NHC_NGG_Compare.ne,NHC_NGG_Loader.result,bind_tc_ok]
  cases he : account.executable <;> cases hs : account.signer <;> cases hw : account.writable <;>
    by_cases hk : account.key.val = selected.val <;>
    by_cases hl : account.owner.val=a.val ∨ account.owner.val=b.val ∨ account.owner.val=c.val <;>
    simp [he,hs,hw,hk,hl,loader]
#print axioms verifier
theorem token (account : NHC_NGG_Ref.Account) (token_id a b c : Key) :
    NHC_NGG_Ref.token account token_id (NHC_NGG_Loader.loaders a b c) =
      ok (if account.key.val ≠ token_id.val ∨ account.executable = false ∨ account.signer = true ∨ account.writable = true ∨ loader account.owner a b c = false
        then .Err NHC_NGG_Ref.Error.InvalidTokenProgram else .Ok ()) := by
  simp only [NHC_NGG_Ref.token,NHC_NGG_Compare.ne,NHC_NGG_Loader.result,bind_tc_ok]
  cases he : account.executable <;> cases hs : account.signer <;> cases hw : account.writable <;>
    by_cases hk : account.key.val = token_id.val <;>
    by_cases hl : account.owner.val=a.val ∨ account.owner.val=b.val ∨ account.owner.val=c.val <;>
    simp [he,hs,hw,hk,hl,loader]
#print axioms token
end NHC_NGG_Metadata

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
