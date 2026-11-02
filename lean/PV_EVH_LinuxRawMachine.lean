import PV_EVH_LinuxRawABI
import PV_EVH_LinuxRawFrame
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawMachine
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawABI (Inputs inputs signed modulus)
open PV_EVH_Runtime (Outcome)
open PV_EVH_World (World)
variable [ExternalTypes]

/-- A register return is a machine word. Memory, world and every observation
prefix remain independent components, including on faults and exhaustion.
An actual instance of this interface and its kernel footprint remain P. -/
structure Reply where
  result : Outcome (Fin modulus)
  buffer : Array U8 64#usize
  world : World
  events : List PV_RJ4IDB.NativeEvent

def decode : Outcome (Fin modulus) → Outcome Int
  | .returned (.ok n) => .returned (.ok (signed n.val))
  | .returned (.fail e) => .returned (.fail e)
  | .returned .div => .returned .div
  | .fault e => .fault e
  | .exhausted => .exhausted

def call (machine : Inputs → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) : PV_EVH_LinuxRawControl.Reply :=
  let r := machine (inputs address length) a w
  ⟨decode r.result,r.buffer,r.world,r.events⟩

theorem retained (machine : Inputs → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) :
    let r := machine (inputs address length) a w
    (call machine address length a w).buffer = r.buffer ∧
    (call machine address length a w).world = r.world ∧
    (call machine address length a w).events = r.events := ⟨rfl,rfl,rfl⟩

theorem returned (machine : Inputs → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) (n : Fin modulus)
    (h : (machine (inputs address length) a w).result = .returned (.ok n)) :
    (call machine address length a w).result = .returned (.ok (signed n.val)) ∧
    -(PV_EVH_LinuxRawABI.half : Int) ≤ signed n.val ∧
    signed n.val < (PV_EVH_LinuxRawABI.half : Int) := by
  exact ⟨by simp only [call,h,decode],PV_EVH_LinuxRawABI.signed_range n.val n.isLt⟩

theorem fault (machine : Inputs → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World) (e : PV_EVH_Runtime.Fault)
    (h : (machine (inputs address length) a w).result = .fault e) :
    (call machine address length a w).result = .fault e := by
  simp only [call,h,decode]

theorem exhausted (machine : Inputs → Array U8 64#usize → World → Reply)
    (address length : Nat) (a : Array U8 64#usize) (w : World)
    (h : (machine (inputs address length) a w).result = .exhausted) :
    (call machine address length a w).result = .exhausted := by
  simp only [call,h,decode]

/-- The footprint is transported, never inferred from the entropy density
law or from a successful return. This includes all raw terminal prefixes. -/
theorem kernel_frame (machine : Inputs → Array U8 64#usize → World → Reply)
    (address : Nat)
    (h : ∀ offset, offset ≤ 64 → ∀ a w,
      PV_EVH_LinuxRawFrame.Prefix
        (machine (inputs (address+offset) (64-offset)) a w).buffer a offset) :
    PV_EVH_LinuxRawFrame.KernelFrame (call machine) address := h

#print axioms retained
#print axioms returned
#print axioms fault
#print axioms exhausted
#print axioms kernel_frame
end PV_EVH_LinuxRawMachine
