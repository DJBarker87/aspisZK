import PV_EVH_KernelMemory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_KernelPrefix
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_KernelMemory (Memory Backed Step ValidAnswer)

theorem byte_ext (x y : U8) (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

/-- The weaker source-prefix law follows from the SAME physical syscall
memory, rather than being a second independently supplied kernel premise. -/
theorem step_prefix (address offset : Nat) (before after : Memory)
    (a old : Array U8 64#usize) (ho : offset ≤ 64)
    (hb : Backed address old before) (hs : Step address offset before after a) :
    PV_EVH_LinuxRawFrame.Prefix a old offset := by
  intro i hi
  have hai : i < a.val.length := by rw [a.property]; change i < 64; omega
  have hoi : i < old.val.length := by rw [old.property]; change i < 64; omega
  have ha := List.getElem?_eq_getElem hai
  have hold := List.getElem?_eq_getElem hoi
  have he := (PV_EVH_KernelMemory.consumed address offset before after a old hb hs i hi (by omega)).2
  rw [PV_EVH_StackByteCodec.encode_read a i _ ha,
    PV_EVH_StackByteCodec.encode_read old i _ hold] at he
  rw [ha,hold]
  exact congrArg some (byte_ext _ _ he)

/-- One retained runtime KERNEL-WRITE instance entails every old KernelFrame
consumer. This implication is unconditional in raw status and fuel; it supplies
neither the actual OS instance nor a successful entropy/prover witness. -/
theorem kernel_frame
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (memory : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → Memory → Memory)
    (address : Nat) (hk : ValidAnswer kernel memory address) :
    PV_EVH_LinuxRawFrame.KernelFrame kernel address := by
  intro offset ho a w
  let m : Memory := fun p => ((PV_EVH_StackEntropyFill.encode a)[p-address]?.getD 0).toNat
  have hb : Backed address a m := by
    intro i hi
    simp only [m,Nat.add_sub_cancel_left]
  exact step_prefix address offset m _ _ a ho hb (hk offset ho a w m hb)

#print axioms byte_ext
#print axioms step_prefix
#print axioms kernel_frame
end PV_EVH_KernelPrefix
