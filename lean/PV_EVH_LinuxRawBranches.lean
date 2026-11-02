import PV_EVH_LinuxRawControl
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawBranches
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl
open PV_EVH_World (World)
variable [ExternalTypes]
variable (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
variable (address fuel offset : Nat) (a : Array U8 64#usize) (w : World)

/-- Zero return is UNEXPECTED, retaining every supplied byte and event. -/
theorem zero (r : Reply) (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok 0)) :
    loop syscall address (fuel+1) offset a w =
      ⟨.returned (.ok (.Err unexpected)),r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr,Int.le_refl,if_true]

/-- EINTR repeats the remaining slice, not the whole buffer. -/
theorem interrupted (r : Reply) (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok (-4))) :
    loop syscall address (fuel+1) offset a w =
      let d := loop syscall address fuel offset r.buffer r.world
      {d with events := r.events ++ d.events} := by
  simp only [loop,hs,hr]
  rfl

theorem partial (r : Reply) (ret : Int)
    (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok ret)) (hpos : 0 ≤ ret) (hne : ret ≠ 0)
    (hfit : ret.toNat ≤ 64-offset) (hmore : offset+ret.toNat ≠ 64) :
    loop syscall address (fuel+1) offset a w =
      let d := loop syscall address fuel (offset+ret.toNat) r.buffer r.world
      {d with events := r.events ++ d.events} := by
  simp only [loop,hs,hr,if_pos hpos,if_neg hne,if_pos hfit,if_neg hmore]

theorem complete (r : Reply) (ret : Int)
    (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok ret)) (hpos : 0 ≤ ret) (hne : ret ≠ 0)
    (hfit : ret.toNat ≤ 64-offset) (hend : offset+ret.toNat = 64) :
    loop syscall address (fuel+1) offset a w =
      ⟨.returned (.ok (.Ok ())),r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr,if_pos hpos,if_neg hne,if_pos hfit,if_pos hend]

theorem oversized (r : Reply) (ret : Int)
    (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok ret)) (hpos : 0 ≤ ret) (hne : ret ≠ 0)
    (hfit : ¬ ret.toNat ≤ 64-offset) :
    loop syscall address (fuel+1) offset a w =
      ⟨.returned (.ok (.Err unexpected)),r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr,if_pos hpos,if_neg hne,if_neg hfit]

theorem negative (r : Reply) (ret : Int)
    (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok ret)) (hneg : ¬ 0 ≤ ret) (hintr : ret ≠ -4)
    (hfit : -(2147483648 : Int) ≤ ret) :
    loop syscall address (fuel+1) offset a w =
      ⟨.returned (.ok (.Err ret)),r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr,if_neg hneg,if_neg hintr,if_pos hfit]

theorem negative_overflow (r : Reply) (ret : Int)
    (hs : syscall (address+offset) (64-offset) a w = r)
    (hr : r.result = .returned (.ok ret)) (hneg : ¬ 0 ≤ ret) (hintr : ret ≠ -4)
    (hfit : ¬ -(2147483648 : Int) ≤ ret) :
    loop syscall address (fuel+1) offset a w =
      ⟨.returned (.ok (.Err unexpected)),r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr,if_neg hneg,if_neg hintr,if_neg hfit]

theorem fault (r : Reply) (e : PV_EVH_Runtime.Fault)
    (hs : syscall (address+offset) (64-offset) a w = r) (hr : r.result = .fault e) :
    loop syscall address (fuel+1) offset a w = ⟨.fault e,r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr]

theorem exhausted (r : Reply)
    (hs : syscall (address+offset) (64-offset) a w = r) (hr : r.result = .exhausted) :
    loop syscall address (fuel+1) offset a w = ⟨.exhausted,r.buffer,r.world,r.events⟩ := by
  simp only [loop,hs,hr]

#print axioms zero
#print axioms interrupted
#print axioms partial
#print axioms complete
#print axioms oversized
#print axioms negative
#print axioms negative_overflow
#print axioms fault
#print axioms exhausted
end PV_EVH_LinuxRawBranches
