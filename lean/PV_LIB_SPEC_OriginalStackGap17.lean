import PV_LIB_SPEC_BinaryStack16
import PV_LIB_SPEC_EntryPre14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_OriginalStackGap17
open PV_LIB_SPEC_BinaryStack16

/-- Adopted ELF fc8808eb, f8eef LEA 0x70(%rsp),%rsi;
f8ef4 CALL fac90 pushes8 bytes. Together with the checked scope/spawn
prologues, this is the native ABI constraint on the incoming run address.
This predicate is a diagnostic target, never a new row premise. -/
def NativePair (entryRsp runPointer : Nat) : Prop :=
  360 ≤ entryRsp ∧ runPointer = entryRsp + 0x78

/-- Physical run address retained by the ORIGINAL Entry14 capture. -/
theorem original_run_base :
    PV_LIB_SPEC_ConcreteCaptures.runHeader.pointer = 112 := rfl

/-- SPEC-C13: no natural-address native scope/spawn stack can have the
retained physical run112 and the adopted caller's actual RSI relation.
This refutes this local pairing, NOT Cut92Composition.Witness. -/
theorem original_pair_impossible (entryRsp : Nat) : ¬ NativePair entryRsp 112 := by
  intro h
  obtain ⟨bound,pair⟩ := h
  omega

/-- Repair of the coordinate specification: derive the physical run pointer
from the native CALL boundary, rather than choose it independently. This
still needs capture-memory relocation and the original stack grant. -/
def pairedFrame (entryRsp activation : Nat) : PV_LIB_SPEC_PhysicalStack12.Frame :=
  frame entryRsp (entryRsp+0x78) activation

theorem repaired_pair (entryRsp : Nat) (activation : Nat) (bound : 360 ≤ entryRsp) :
    NativePair entryRsp (pairedFrame entryRsp activation).runPointer :=
  ⟨bound,rfl⟩

theorem repaired_excludes_original (entryRsp activation : Nat) (bound : 360 ≤ entryRsp) :
    (pairedFrame entryRsp activation).runPointer ≠ 112 := by
  intro equal
  have pair := repaired_pair entryRsp activation bound
  rw [equal] at pair
  exact original_pair_impossible entryRsp pair

#print axioms NativePair
#print axioms original_run_base
#print axioms original_pair_impossible
#print axioms pairedFrame
#print axioms repaired_pair
#print axioms repaired_excludes_original
end PV_LIB_SPEC_OriginalStackGap17
