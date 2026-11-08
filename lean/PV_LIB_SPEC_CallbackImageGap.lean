import PV_LIB_SPEC_AllocationImages
import PV_LIB_SPEC_LocalOwnership
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackImageGap
open PV_EVHB_OwnerMachine
open PV_LIB_SPEC_AllocationImages

/-- Source13923's installed ownership/backing allocation has NO byte suffix.
This checks the successful56-byte resource reply already used in session8,
without normalizing any original-entry recurrence. -/
theorem allocation_memory :
    PV_LIB_SPEC_LocalOwnership.allocated.world.memory 8224 = none := rfl

/-- At adopted ELF fc8808eb..., e061d ALWAYS stores r12 at callback offset32.
Even zero-valued bytes are stores: they must not remain unknown destination
bytes. The stack-copy operands are unrestricted in this local comparison. -/
theorem binary_memory (snapshot : Memory) (rsp packetPointer capturePointer captureLength : Nat)
    (before : Memory) :
    overwrite 8192 (callback snapshot rsp packetPointer capturePointer captureLength) before 8224 =
      some (byte packetPointer 0).val := by
  apply stored 8192 32
  rfl

/-- Exact complete-memory disagreement between the installed13923 allocation
and the adopted store cut, for ALL copied stack bytes and actual r12/rcx/rax
operands. This is a LOCAL interpretation contradiction, not a theorem about
reachability or the full composed existential. -/
theorem memory_disagrees (snapshot : Memory) (rsp packetPointer capturePointer captureLength : Nat) :
    PV_LIB_SPEC_LocalOwnership.allocated.world.memory ≠
      overwrite 8192 (callback snapshot rsp packetPointer capturePointer captureLength)
        PV_LIB_SPEC_LocalOwnership.allocated.world.memory := by
  intro equal
  have cell := congrFun equal 8224
  rw [allocation_memory,binary_memory] at cell
  cases cell

/-- A known-byte serializer also fails on a real copy of an unknown stack byte.
The new Image distinguishes this case from a no-store hole. This rules out
repair by replacing callback stack padding with chosen initialized bytes. -/
theorem unknown_copy (snapshot : Memory) (rsp p packetPointer capturePointer captureLength : Nat)
    (unknown : snapshot (rsp+0x38) = none) (value : Nat) :
    overwrite p (callback snapshot rsp packetPointer capturePointer captureLength) snapshot p ≠ some value := by
  have copied := callback_copy p rsp packetPointer capturePointer captureLength 0 snapshot (by decide)
  simpa only [Nat.add_zero,unknown] using (show
    overwrite p (callback snapshot rsp packetPointer capturePointer captureLength) snapshot (p+0) ≠ some value by
      rw [copied,Nat.add_zero,unknown]; intro impossible; cases impossible)

#print axioms allocation_memory
#print axioms binary_memory
#print axioms memory_disagrees
#print axioms unknown_copy
end PV_LIB_SPEC_CallbackImageGap
