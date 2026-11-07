import PCF_AccountRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_AccountLaws

def payerModel (signer writable executable system_owner system_key native_owner
    system_executable system_signer system_writable : Bool) : U32 :=
  if !(signer && writable && !executable && system_owner) then 0x41532034#u32
  else if !(system_key && native_owner && system_executable && !system_signer && !system_writable)
    then 0x41532033#u32 else 0#u32

theorem payer (signer writable executable system_owner system_key native_owner
    system_executable system_signer system_writable : Bool) :
    PCF_AccountRef.payer_reference signer writable executable system_owner system_key
      native_owner system_executable system_signer system_writable =
      ok (payerModel signer writable executable system_owner system_key native_owner
        system_executable system_signer system_writable) := by
  cases signer <;> cases writable <;> cases executable <;> cases system_owner <;>
    cases system_key <;> cases native_owner <;> cases system_executable <;>
    cases system_signer <;> cases system_writable <;> rfl

def tokenModel (token_key executable signer writable bpf_owner upgradeable_owner v4_owner : Bool) : U32 :=
  if token_key && executable && !signer && !writable && (bpf_owner || upgradeable_owner || v4_owner)
    then 0#u32 else 0x41532013#u32

theorem token (token_key executable signer writable bpf_owner upgradeable_owner v4_owner : Bool) :
    PCF_AccountRef.token_reference token_key executable signer writable bpf_owner
      upgradeable_owner v4_owner =
      ok (tokenModel token_key executable signer writable bpf_owner upgradeable_owner v4_owner) := by
  cases token_key <;> cases executable <;> cases signer <;> cases writable <;>
    cases bpf_owner <;> cases upgradeable_owner <;> cases v4_owner <;> rfl

#print axioms payer
#print axioms token
end PCF_AccountLaws
