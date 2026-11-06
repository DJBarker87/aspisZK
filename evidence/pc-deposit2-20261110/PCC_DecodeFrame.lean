import PCC_DepositDecodeReference
import PCC_ReferenceInvariant
set_option autoImplicit false
namespace PCC
open PCA

theorem decode_frame (bytes : Bytes) (s : PCA_State) :
    (decodeReference bytes s).state = s ∧ (decodeReference bytes s).events = [] := ⟨rfl,rfl⟩
theorem decode_preserves (bytes : Bytes) : Preserves (decodeReference bytes) := fun _ h => h
/-- The FIRST length check rejects without entering any digest conversion. -/
theorem decode_length_rejection (bytes : Bytes) (s : PCA_State)
    (h : bytes.length < 80 ∨ bytes.length > 592) :
    decodeReference bytes s = ⟨s,[],.error (.deposit .WrongLength)⟩ := by
  rcases h with h | h <;> simp [decodeReference,h]
#print axioms decode_frame
#print axioms decode_preserves
#print axioms decode_length_rejection
end PCC
