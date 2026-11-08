import PV_STX2_CopyReplyInterpretation
import PV_OWN2_ByteFrame
set_option autoImplicit false
noncomputable section
namespace PV_STX2_CopySourceFrame
open PV_EVHB_OWNER PV_OWN2_FreshAllocation
/-- Conditional on owner acceptance of the translator patch. Once allocation
separation is derived by the named byte-frame law, every byte in the supplied
source region is unchanged by the documented intrinsic update. -/
theorem source (w : OWNER) (src sourceBytes dst count offset : Nat)
    (apart : RangeDisjoint src sourceBytes dst (count*4))
    (within : offset < sourceBytes) :
    (PV_EVHB_OwnerHeap.copied w src dst (count*4)).world.memory (src+offset) =
      w.world.memory (src+offset) := by
  change (if dst ≤ src+offset ∧ src+offset < dst+count*4 then
    w.world.memory (src+(src+offset-dst)) else w.world.memory (src+offset)) = _
  have outside : ¬ (dst ≤ src+offset ∧ src+offset < dst+count*4) := by
    rcases apart with before | after <;> omega
  exact if_neg outside
/-- Conditional on owner acceptance of the translator patch. Applying the
OWNER copy after the interpreted native success is idempotent on bytes under
the same separation. This prevents double application from corrupting source
reads when connecting the reply interpretation to the existing action table. -/
theorem idempotent (w : OWNER) (src dst count : Nat)
    (apart : RangeDisjoint src (count*4) dst (count*4)) :
    (PV_EVHB_OwnerHeap.copied (PV_EVHB_OwnerHeap.copied w src dst (count*4)) src dst (count*4)).world.memory =
      (PV_EVHB_OwnerHeap.copied w src dst (count*4)).world.memory := by
  funext address
  by_cases inside : dst ≤ address ∧ address < dst+count*4
  · change PV_EVHB_OwnerHeap.copyMemory _ src dst (count*4) address = _
    rw [PV_EVHB_OwnerHeap.copyMemory,if_pos inside]
    have offset : address-dst < count*4 := by omega
    have target : (PV_EVHB_OwnerHeap.copied w src dst (count*4)).world.memory address =
        w.world.memory (src+(address-dst)) := by
      simpa only [Nat.add_sub_of_le inside.1] using
        PV_STX2_OwnerCopiedBytes.copied_byte w src dst (count*4) (address-dst) offset
    exact (source w src (count*4) dst count (address-dst) apart offset).trans target.symm
  · change PV_EVHB_OwnerHeap.copyMemory _ src dst (count*4) address = _
    rw [PV_EVHB_OwnerHeap.copyMemory,if_neg inside]
#print axioms source
#print axioms idempotent
end PV_STX2_CopySourceFrame
