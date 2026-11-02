import PV_EVH_LinuxRawBounds
import PV_EVH_EntropySourceSlot
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawSpatial
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply)
open PV_EVH_LinuxRawHistory (execute Call)
open PV_EVH_StackZero (State)

/-- Derive every request's heap/live disjointness from the original frame's
admission, rather than postulating independent frames for retries and partial
reads. Actual original-frame provenance is still a separate P obligation. -/
theorem request_separation
    (syscall : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → Reply)
    (owner address fuel : Nat) (a : Array U8 64#usize) (w : State)
    (hs : PV_EVH_StackAdmission.HeapSeparate
      (PV_EVH_EntropySourceSlot.original owner address w) w)
    (hl : PV_EVH_StackAdmission.LiveSeparate
      (PV_EVH_EntropySourceSlot.original owner address w) w)
    (c : Call) (hc : c ∈ (execute syscall address fuel 0 a w.frame.runtime.base).calls)
    (i : Nat) (hi : i < c.length) :
    (∀ b ∈ w.frame.runtime.heap, ∀ j, j < b.bytes.length →
      c.address+i ≠ b.address+j) ∧
    (∀ old ∈ w.frame.live, ∀ j, j < old.initialized →
      c.address+i ≠ old.address+j) := by
  have hb := PV_EVH_LinuxRawBounds.byte_inside syscall address fuel a
    w.frame.runtime.base c hc i hi
  constructor
  · intro b hm j hj he
    have h := hs b hm j hj
    change b.address+j < address ∨ address+64 ≤ b.address+j at h
    omega
  · intro old hm j hj he
    have h := hl old hm j hj
    change old.address+j < address ∨ address+64 ≤ old.address+j at h
    omega

#print axioms request_separation
end PV_EVH_LinuxRawSpatial
