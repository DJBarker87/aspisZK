import PV_EVH_RawMemoryHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RawMemoryReification
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_KernelMemory (Backed Step ValidAnswer)
open PV_EVH_RawMemoryHistory (MemoryAnswer replay)
open PV_EVH_LinuxRawHistory (execute)
open PV_EVH_StackZero (Slot State)

/-- The initializer supplies the first physical backing relation. Freshness,
valid writable memory, and actual call-frame interpretation remain FRAME-ENTRY. -/
theorem admitted (slot : Slot) (a : Array U8 64#usize) (w : State)
    (hn : slot.initialized = 64) :
    Backed slot.address a (PV_EVH_StackAdmission.enter slot
      (PV_EVH_StackEntropyFill.encode a) w).memory := by
  intro i hi
  exact PV_EVH_StackAdmission.write_inside slot _ w i (by omega)

/-- From the runtime's per-syscall KERNEL-WRITE law, derive whole-driver
physical backing and outside-original preservation on ALL source outcomes and
finite prefixes. Requests, replies and memory share one existing raw history.
This does not prove the runtime KERNEL-WRITE instance or compiler fidelity. -/
theorem all_outcomes
    (syscall : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (memory : MemoryAnswer) (slot : Slot) (fuel : Nat)
    (a : Array U8 64#usize) (w : State)
    (hn : slot.initialized = 64) (hk : ValidAnswer syscall memory slot.address)
    (hb : Backed slot.address a w.memory) :
    let e := execute syscall slot.address fuel 0 a w.frame.runtime.base
    replay memory e.calls w.memory =
      (PV_EVH_StackAdmission.write slot (PV_EVH_StackEntropyFill.encode e.delivery.buffer) w).memory := by
  dsimp only
  have hs := PV_EVH_LinuxRawBounds.requests syscall slot.address fuel 0 a
    w.frame.runtime.base (by omega)
  have ha := PV_EVH_RawMemoryHistory.answers syscall slot.address fuel 0 a w.frame.runtime.base
  have hv : ∀ c ∈ (execute syscall slot.address fuel 0 a w.frame.runtime.base).calls,
      ∀ before, Backed slot.address c.before before →
      Step slot.address (c.address-slot.address) before
        (memory c.address c.length c.before c.worldBefore before) c.after.buffer := by
    intro c hc before hbefore
    have hcshape := hs c hc
    unfold PV_EVH_LinuxRawBounds.Suffix at hcshape
    have hoff : c.address-slot.address ≤ 64 := by omega
    have hadd : slot.address+(c.address-slot.address) = c.address := by omega
    have hlen : 64-(c.address-slot.address) = c.length := by omega
    have h := hk (c.address-slot.address) hoff c.before c.worldBefore before hbefore
    rw [hadd,hlen,← ha c hc] at h
    exact h
  have h := PV_EVH_RawMemoryHistory.threaded memory slot.address _ a _ _ _ w.memory
    (PV_EVH_LinuxRawThreaded.continuous syscall slot.address fuel 0 a w.frame.runtime.base) hv hb
  apply PV_EVH_KernelMemory.reifies slot 0 w _ _ hn
  exact ⟨h.1,by simpa only [Nat.add_zero] using h.2⟩

/-- Replaces an independent full-post-buffer memory premise for the existing
source-bound driver. The initial backing is supplied by admitted, not an
unrelated helper answer. Events/status/world are those of the unchanged driver. -/
theorem driver_memory [ExternalTypes]
    (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (memory : MemoryAnswer) (slot : Slot) (fuel : Nat) (input : Slice U8) (w : State)
    (hn : slot.initialized = 64) (hk : ValidAnswer syscall memory slot.address)
    (hb : Backed slot.address (Array.repeat 64#usize 0#u8) w.memory) :
    let e := execute syscall slot.address fuel 0 (Array.repeat 64#usize 0#u8) w.frame.runtime.base
    let d := PV_EVH_LinuxRawControl.driver decode syscall slot.address fuel input w
    replay memory e.calls w.memory = (PV_EVH_StackEntropyFill.post slot d w).memory := by
  dsimp only
  have h := all_outcomes syscall memory slot fuel (Array.repeat 64#usize 0#u8) w hn hk hb
  unfold PV_EVH_LinuxRawControl.driver PV_EVH_StackEntropyFill.post
  rw [← PV_EVH_LinuxRawHistory.erases]
  exact h

#print axioms admitted
#print axioms all_outcomes
#print axioms driver_memory
end PV_EVH_RawMemoryReification
