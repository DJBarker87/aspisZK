import PV_EVH_StackCopy
import PV_EVH_StackEntropyFill
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyPhysicalCopy
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackRegions (Separate)
open PV_EVH_StackCopy (copy)

/-- The two source admit_pairrs precede both copies. Addresses and owners are
the caller's physical frame, never chosen from extensional array equality. -/
def admit_pair (field seed : Slot) (w : State) : State :=
  PV_EVH_StackAdmission.enter seed (List.replicate 32 0)
    (PV_EVH_StackAdmission.enter field (List.replicate 32 0) w)

def copies (original field seed : Slot) (w : State) : State :=
  copy original seed 32 (copy original field 0 w)

theorem admit_pair_original (original field seed : Slot) (w : State)
    (hf : Separate field original) (hs : Separate seed original)
    (i : Nat) (hi : i < original.initialized) :
    (admit_pair field seed w).memory (original.address+i) = w.memory (original.address+i) := by
  unfold admit_pair
  change (PV_EVH_StackAdmission.write seed _ _).memory _ = _
  rw [PV_EVH_StackAdmission.write_outside seed _ _ _
    (PV_EVH_StackRegions.outside seed original hs i hi)]
  exact PV_EVH_StackAdmission.write_outside field _ w _
    (PV_EVH_StackRegions.outside field original hf i hi)

theorem original_preserved (original field seed : Slot) (w : State)
    (hf : Separate field original) (hs : Separate seed original)
    (i : Nat) (hi : i < original.initialized) :
    (copies original field seed w).memory (original.address+i) = w.memory (original.address+i) := by
  unfold copies
  rw [PV_EVH_StackCopy.source_preserved original seed 32 _ hs i hi,
    PV_EVH_StackCopy.source_preserved original field 0 w hf i hi]

/-- Physical first32 and second32, from the SAME delivered original buffer.
The second copy reads the still-live original rather than a supplied answer.
Source indexing/restoration is independently bound by NativeEntropyValues.
Actual frame and memcpy association remain P; no native event is omitted here. -/
theorem delivered_halves (original field seed : Slot) (w : State)
    (a : Array U8 64#usize)
    (ho : original.initialized = 64) (hf : field.initialized = 32)
    (hs : seed.initialized = 32)
    (hfo : Separate field original) (hso : Separate seed original)
    (hsf : Separate seed field)
    (hb : ∀ i, i < 64 → w.memory (original.address+i) =
      ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat) :
    let v := copies original field seed (admit_pair field seed w)
    (∀ i, i < 32 → v.memory (field.address+i) =
      ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat) ∧
    (∀ i, i < 32 → v.memory (seed.address+i) =
      ((PV_EVH_StackEntropyFill.encode a)[32+i]?.getD 0).toNat) := by
  dsimp only
  constructor
  · intro i hi
    unfold copies
    rw [PV_EVH_StackCopy.outside original seed 32 _ _
      (PV_EVH_StackRegions.outside seed field hsf i (by omega)),
      PV_EVH_StackCopy.inside original field 0 _ i (by omega),Nat.add_zero]
    exact (admit_pair_original original field seed w hfo hso i (by omega)).trans (hb i (by omega))
  · intro i hi
    unfold copies
    rw [PV_EVH_StackCopy.inside original seed 32 _ i (by omega)]
    rw [Nat.add_assoc original.address 32 i]
    rw [PV_EVH_StackCopy.source_preserved original field 0 _ hfo (32+i) (by omega)]
    exact (admit_pair_original original field seed w hfo hso (32+i) (by omega)).trans
      (hb (32+i) (by omega))

theorem heap_coherent (original field seed : Slot) (w : State)
    (hc : PV_EVH_StackAdmission.HeapCoherent w)
    (hf : PV_EVH_StackAdmission.HeapSeparate field w)
    (hs : PV_EVH_StackAdmission.HeapSeparate seed w) :
    PV_EVH_StackAdmission.HeapCoherent
      (copies original field seed (admit_pair field seed w)) := by
  exact PV_EVH_StackCopy.heap_coherent original seed 32 _
    (PV_EVH_StackCopy.heap_coherent original field 0 _
      (PV_EVH_StackAdmission.enter_heap seed _ _
        (PV_EVH_StackAdmission.enter_heap field _ w hc hf) hs) hf) hs

#print axioms admit_pair_original
#print axioms original_preserved
#print axioms delivered_halves
#print axioms heap_coherent
end PV_EVH_EntropyPhysicalCopy
