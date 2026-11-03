import PV_EVH_LinuxRawFrame
import PV_EVH_StackByteCodec
set_option autoImplicit false
noncomputable section
namespace PV_EVH_KernelMemory
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)

abbrev Memory := Nat → Nat

def Backed (address : Nat) (a : Array U8 64#usize) (m : Memory) : Prop :=
  ∀ i, i < 64 → m (address+i) =
    ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat

/-- Exact runtime KERNEL-WRITE obligation, separate from raw register selection,
compiler preservation and entropy density. The SAME physical post-memory
backs the returned buffer and preserves every byte outside the supplied suffix,
including faults, errors, EINTR and exhausted prefixes. No successful status
is required. The OS instance is still an explicit runtime P obligation. -/
def Step (address offset : Nat) (before after : Memory)
    (a : Array U8 64#usize) : Prop :=
  Backed address a after ∧
  ∀ p, p < address+offset ∨ address+64 ≤ p → after p = before p

/-- An arbitrary answer buffer is insufficient: the actual memory answer must
satisfy this relation on each reached call, not only successful final fills. -/
def ValidAnswer
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (memory : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → Memory → Memory)
    (address : Nat) : Prop :=
  ∀ offset, offset ≤ 64 → ∀ a w m, Backed address a m →
    Step address offset m (memory (address+offset) (64-offset) a w m)
      (kernel (address+offset) (64-offset) a w).buffer

/-- Reification of a completed syscall memory answer is DERIVED from
same-memory backing and its full suffix footprint. It is not an independent
physical write of a fabricated whole-buffer answer. -/
theorem reifies (slot : Slot) (offset : Nat) (w : State)
    (a : Array U8 64#usize) (after : Memory)
    (hn : slot.initialized = 64)
    (h : Step slot.address offset w.memory after a) :
    after = (PV_EVH_StackAdmission.write slot (PV_EVH_StackEntropyFill.encode a) w).memory := by
  funext p
  by_cases hp : slot.address ≤ p ∧ p < slot.address+slot.initialized
  · have hi : p-slot.address < 64 := by omega
    have he : slot.address+(p-slot.address) = p := by omega
    have hb := h.1 (p-slot.address) hi
    rw [he] at hb
    simp only [PV_EVH_StackAdmission.write,if_pos hp]
    exact hb
  · have ho : p < slot.address+offset ∨ slot.address+64 ≤ p := by omega
    simp only [PV_EVH_StackAdmission.write,if_neg hp]
    exact h.2 p ho

/-- All consumed physical bytes are stable on EVERY raw outcome. Unlike
KernelFrame, the conclusion concerns the actual memory answer as well. -/
theorem consumed (address offset : Nat) (before after : Memory)
    (a old : Array U8 64#usize) (hb : Backed address old before)
    (h : Step address offset before after a) (i : Nat)
    (hi : i < offset) (hn : i < 64) :
    after (address+i) = before (address+i) ∧
    ((PV_EVH_StackEntropyFill.encode a)[i]?.getD 0).toNat =
      ((PV_EVH_StackEntropyFill.encode old)[i]?.getD 0).toNat := by
  have he := h.2 (address+i) (Or.inl (by omega))
  exact ⟨he,(h.1 i hn).symm.trans (he.trans (hb i hn))⟩

#print axioms reifies
#print axioms consumed
end PV_EVH_KernelMemory
