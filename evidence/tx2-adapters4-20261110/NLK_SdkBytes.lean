import NLK_ReturningBorrow
import NLK_LaneProgram
set_option autoImplicit false
namespace NLK_SdkBytes
open Aeneas Aeneas.Std
/-- A total coordinate-preserving byte conversion, not a byte oracle. -/
def byte (b : UInt8) : U8 := ⟨b.toNat,by exact b.toNat_lt⟩
/-- Slice extent is explicit. Unbounded SDK ghost payloads are NOT silently
assumed to fit usize; callers derive the bound from their fixed format. -/
def payload (b : NLF_SdkModel.Payload) (bound : b.bytes.length≤Usize.max) : Slice U8 :=
 ⟨b.bytes.map byte,by simpa using bound⟩
theorem byte_value (b : UInt8) : (byte b).val=b.toNat := rfl
theorem payload_length (b : NLF_SdkModel.Payload) (h : b.bytes.length≤Usize.max) :
 (payload b h).val.length=b.bytes.length := List.length_map _
theorem payload_values (b : NLF_SdkModel.Payload) (h : b.bytes.length≤Usize.max) :
 (payload b h).val.map UScalar.val=b.bytes.map UInt8.toNat := by
 simp only [payload,List.map_map];rfl
/-- The lane caller's bound is proved, not a new entry admission premise. -/
theorem lane_bound (b : NLF_SdkModel.Payload) (size : b.bytes.length=768) :
 b.bytes.length≤Usize.max := by rw [size];scalar_tac
#print byte_value
#print axioms byte_value
#print payload_length
#print axioms payload_length
#print payload_values
#print axioms payload_values
#print lane_bound
#print axioms lane_bound
end NLK_SdkBytes
