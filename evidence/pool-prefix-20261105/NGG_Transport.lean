import NGG_Compare
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_Transport
abbrev Key := NGG_Compare.Key
def value (program proof : NGG_Ref.Account) (checkpoint : Option NGG_Ref.Account) :
    core.result.Result Key NGG_Ref.Error :=
  match checkpoint with
  | none => .Err .NotEnoughAccountKeys
  | some c => if proof.key.val = program.key.val ∨ proof.executable = true ∨ proof.signer = true ∨ proof.writable = true ∨ c.owner.val ≠ program.key.val ∨ c.executable = true ∨ c.signer = true ∨ c.writable = true ∨ c.key.val = proof.key.val ∨ c.key.val = program.key.val
    then .Err .InvalidVerifierProof else .Ok program.key

theorem result (program proof : NGG_Ref.Account) (checkpoint : Option NGG_Ref.Account) :
    NGG_Ref.transport program proof checkpoint = ok (value program proof checkpoint) := by
  cases checkpoint with
  | none => rfl
  | some c =>
    simp only [NGG_Ref.transport,NGG_Ref.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      NFV_RequestGuards.array,NGG_Compare.ne,value]
    split_ifs <;> simp_all
#print axioms result
end NGG_Transport
