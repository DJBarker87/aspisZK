import PCC_ErrorTransport
set_option autoImplicit false
namespace PCC
/-- ABI equality is deliberately not claimed to reconstruct payloads. Full
ProgramError values stay available until the audited observation point. -/
theorem full_borsh_injective (x y : String)
    (h : ProgramError.BorshIoError x = ProgramError.BorshIoError y) : x = y :=
  ProgramError.BorshIoError.inj h

theorem borsh_related (x y : String) :
    AbiRelated (α := Unit) (.error (.BorshIoError x)) (.error (.BorshIoError y)) := rfl
#print axioms full_borsh_injective
#print axioms borsh_related
end PCC
