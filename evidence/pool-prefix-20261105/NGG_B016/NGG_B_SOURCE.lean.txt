import NGG_Compare
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_Payer
abbrev Key := NGG_Compare.Key
theorem result (payer system : NGG_Ref.Account) (system_id native_id : Key) :
    NGG_Ref.payer payer system system_id native_id = ok
      (if payer.signer = false ∨ payer.writable = false ∨ payer.executable = true ∨ payer.owner.val ≠ system_id.val
       then .Err NGG_Ref.Error.InvalidPayer
       else if system.key.val ≠ system_id.val ∨ system.owner.val ≠ native_id.val ∨ system.executable = false ∨ system.signer = true ∨ system.writable = true
       then .Err NGG_Ref.Error.InvalidSystemProgram else .Ok ()) := by
  simp only [NGG_Ref.payer,NGG_Compare.ne,bind_tc_ok]
  split_ifs <;> simp_all
#print axioms result
end NGG_Payer
