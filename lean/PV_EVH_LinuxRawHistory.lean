import PV_EVH_LinuxRawControl
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawHistory
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply Delivery unexpected)
open PV_EVH_World (World)

/-- Private execution evidence, NOT a NativeEvent or public observation. Full
before/after buffers survive even on EINTR/error/fault/exhaustion. Connecting
these physical writes and compiler spills to L3 remains a proof obligation. -/
structure Call where
  address : Nat
  length : Nat
  before : Array U8 64#usize
  worldBefore : World
  after : Reply

structure Execution where
  delivery : Delivery
  calls : List Call

def execute (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address : Nat) : Nat → Nat → Array U8 64#usize → World → Execution
  | 0, _, buffer, world => ⟨⟨.exhausted,buffer,world,[]⟩,[]⟩
  | fuel+1, offset, buffer, world =>
    let r := syscall (address+offset) (64-offset) buffer world
    let current : Call := ⟨address+offset,64-offset,buffer,world,r⟩
    let terminal := fun status => (⟨⟨status,r.buffer,r.world,r.events⟩,[]⟩ : Execution)
    let again := fun next =>
      let e := execute syscall address fuel next r.buffer r.world
      (⟨{e.delivery with events := r.events ++ e.delivery.events},e.calls⟩ : Execution)
    let tail := match r.result with
    | .fault e => terminal (.fault e)
    | .exhausted => terminal .exhausted
    | .returned (.fail e) => terminal (.returned (.fail e))
    | .returned .div => terminal (.returned .div)
    | .returned (.ok ret) =>
      if 0 ≤ ret then
        if ret = 0 then terminal (.returned (.ok (.Err unexpected)))
        else if ret.toNat ≤ 64-offset then
          if offset+ret.toNat = 64 then terminal (.returned (.ok (.Ok ())))
          else again (offset+ret.toNat)
        else terminal (.returned (.ok (.Err unexpected)))
      else if ret = -4 then again offset
      else if -(2147483648 : Int) ≤ ret then terminal (.returned (.ok (.Err ret)))
      else terminal (.returned (.ok (.Err unexpected)))
    {tail with calls := current :: tail.calls}

/-- Private instrumentation erases to precisely the source-bound driver, on
all answers and all finite prefixes; it does not change its native events. -/
theorem erases (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    (execute syscall address fuel offset a w).delivery =
      PV_EVH_LinuxRawControl.loop syscall address fuel offset a w := by
  induction fuel generalizing offset a w with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute,PV_EVH_LinuxRawControl.loop]
    cases hr : (syscall (address+offset) (64-offset) a w).result with
    | fault e => rfl
    | exhausted => rfl
    | returned r =>
      cases r with
      | fail e => rfl
      | div => rfl
      | ok ret =>
        split
        next hpos =>
          split
          next hz => rfl
          next hnz =>
            split
            next hfit =>
              split
              next hend => rfl
              next hmore => simp only [ih]
            next hlarge => rfl
        next hneg =>
          split
          next hintr => simp only [ih]
          next hother => split <;> rfl

theorem first_call (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    (execute syscall address (fuel+1) offset a w).calls.head? =
      some ⟨address+offset,64-offset,a,w,syscall (address+offset) (64-offset) a w⟩ := rfl

#print axioms erases
#print axioms first_call
end PV_EVH_LinuxRawHistory
