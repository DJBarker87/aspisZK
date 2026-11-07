import NCV_Reject
import NMX_R3_LaneLength
set_option autoImplicit false
namespace NMX_R3_ReferenceLength
open Aeneas Aeneas.Std RSL

def bytes (b : Slice U8) : Bytes := b.val.map (fun x => UInt8.ofNat x.val)
/-- Full nonexpected-length arm of the pinned emitted reference, with its
installed ProgramError mapping. This is model-side evidence only. -/
theorem emitted (b : Slice U8) (wrong : b.val.length ≠ 768) :
    NCV_Install.op50 b = .ok (.Err .InvalidAccountData) := NCV_Reject.op50 b wrong

theorem canonical (b : Slice U8) (wrong : b.val.length ≠ 768) :
    TX2_217.Ref (bytes b) = RS.throw .invalidAccountData := by
  apply NMX_R3_LaneLength.reference
  simpa only [bytes, List.length_map] using (show b.val.length ≠ LANE_ACCOUNT_BYTES from wrong)
#print axioms emitted
#print axioms canonical
end NMX_R3_ReferenceLength
