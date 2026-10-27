import R1Z.PV_AL_MoveFacts
import R1Z.PV_AL_PopWorld
open Aeneas Aeneas.Std
namespace R1Z.PV_AL_MoveMemory
set_option autoImplicit false

/-- Data-buffer/external bytes. The vector header is carried separately. -/
abbrev Memory := Nat → Option U8

/-- Snapshot-copy semantics of the raw memmove primitive. No allocator or
payload destructor is invoked by this primitive. -/
def copyBytes (memory : Memory) (src dst count : Nat) : Memory :=
  fun i => if dst ≤ i ∧ i < dst+count then memory (src+(i-dst)) else memory i

theorem copy_zero (memory : Memory) (src dst : Nat) : copyBytes memory src dst 0=memory := by
  funext i
  simp only [copyBytes,Nat.add_zero,if_neg (by omega : ¬(dst ≤ i ∧ i<dst))]

/-- The source remove(last) byte-copy count is zero for every element width,
including non-Copy zero-sized payloads. -/
theorem last_copy (memory : Memory) (address n width : Nat) (hn : 0<n) :
    copyBytes memory (address+n*width) (address+(n-1)*width) ((n-(n-1)-1)*width)=memory := by
  rw [PV_AL_MoveFacts.zero_copy n hn,Nat.zero_mul,copy_zero]

structure Observation (T F : Type) where
  returned : Option T
  remaining : alloc.vec.Vec T
  buffer : Nat
  capacity : Nat
  world : PV_AL_PopWorld.World
  memory : Memory
  frame : F

#print axioms copyBytes
#print axioms copy_zero
#print axioms last_copy
end R1Z.PV_AL_MoveMemory
