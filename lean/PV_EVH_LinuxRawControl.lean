import PV_EVH_StackEntropyFill
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawControl
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_Runtime (Outcome)
open PV_EVH_StackZero (State)
open PV_EVH_World (World)
variable [ExternalTypes]

/-- Raw syscall boundary. The full mutable buffer and observation prefix survive
all returns. Its memory-footprint law and kernel association remain P, under the
existing entropy_kernel/compiler obligations; this is not an extra trust item. -/
structure Reply where
  result : Outcome Int
  buffer : Array U8 64#usize
  world : World
  events : List PV_RJ4IDB.NativeEvent

structure Delivery where
  status : Outcome (core.result.Result Unit Int)
  buffer : Array U8 64#usize
  world : World
  events : List PV_RJ4IDB.NativeEvent

/-- Error::UNEXPECTED = INTERNAL_START + 2, on the deployed non-UEFI target. -/
def unexpected : Int := 65538

/-- Source-ordered linux_raw::fill_inner control. The integer carrier retains
negative OS errors exactly. Fuel exhaustion is an interpreter prefix, never an
extra Rust error. The caller has an initialized 64-byte destination. -/
def loop (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address : Nat) : Nat → Nat → Array U8 64#usize → World → Delivery
  | 0, _, buffer, world => ⟨.exhausted,buffer,world,[]⟩
  | fuel+1, offset, buffer, world =>
    let r := syscall (address+offset) (64-offset) buffer world
    let terminal := fun status => (⟨status,r.buffer,r.world,r.events⟩ : Delivery)
    let again := fun next =>
      let d := loop syscall address fuel next r.buffer r.world
      {d with events := r.events ++ d.events}
    match r.result with
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

/-- The opaque extraction's op7 representation is mapped explicitly. Binding
this map to the deployed NonZeroI32 wrapper remains separate from control. -/
def status (decode : Int → getrandom.error.Error) :
    Outcome (core.result.Result Unit Int) → Outcome (core.result.Result Unit getrandom.error.Error)
  | .returned (.ok (.Ok ())) => .returned (.ok (.Ok ()))
  | .returned (.ok (.Err e)) => .returned (.ok (.Err (decode e)))
  | .returned (.fail e) => .returned (.fail e)
  | .returned .div => .returned .div
  | .fault e => .fault e
  | .exhausted => .exhausted

/-- No libc errno call, allocator call, or handle mutation occurs in this source
cone. Only the OS world and mutable output buffer are updated. The source
binding records the selected non-MSAN x86_64 code and the syscall boundary. -/
def driver (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (_input : Slice U8) (w : State) : PV_EVH_StackEntropyFill.Delivery :=
  let d := loop syscall address fuel 0 (Array.repeat 64#usize 0#u8) w.frame.runtime.base
  ⟨status decode d.status,d.buffer,{w.frame.runtime with base := d.world},d.events⟩

theorem heap_preserved (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (input : Slice U8) (w : State) :
    (driver decode syscall address fuel input w).runtime.heap = w.frame.runtime.heap := rfl

theorem errno_preserved (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (input : Slice U8) (w : State) :
    (driver decode syscall address fuel input w).runtime.errno = w.frame.runtime.errno := rfl

theorem allocator_preserved (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (input : Slice U8) (w : State) :
    (driver decode syscall address fuel input w).runtime.allocator = w.frame.runtime.allocator := rfl

theorem handles_preserved (decode : Int → getrandom.error.Error)
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel : Nat) (input : Slice U8) (w : State) :
    (driver decode syscall address fuel input w).runtime.handles = w.frame.runtime.handles := rfl

#print axioms heap_preserved
#print axioms errno_preserved
#print axioms allocator_preserved
#print axioms handles_preserved
end PV_EVH_LinuxRawControl
