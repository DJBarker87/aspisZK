import PV_EVH_StackAdmission
import PV_EVH_NativeEntropyError
set_option autoImplicit false
noncomputable section
namespace PV_EVH_StackEntropyFill
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (Run Q sameKey)
open PV_EVH_Runtime (Outcome)
variable [ExternalTypes]

def encode {n : Usize} (a : Array U8 n) : PV_RJ4IDB.Bytes :=
  a.val.map (fun x => UInt8.ofNat x.val)

/-- The driver's full post-buffer is retained even after an error, fault or
exhaustion. Binding this answer to the deployed getrandom driver remains a P
obligation; the record is not an additional trust item or a success domain. -/
structure Delivery where
  status : Outcome (core.result.Result Unit getrandom.error.Error)
  buffer : Array U8 64#usize
  runtime : PV_EVH_Runtime.State
  events : List PV_RJ4IDB.NativeEvent

def post (slot : Slot) (d : Delivery) (w : State) : State :=
  let f : PV_EVH_StackZero.Frame := ⟨d.runtime,w.frame.live,w.frame.retired⟩
  {PV_EVH_StackAdmission.write slot (encode d.buffer) w with frame := f}

def reply (d : Delivery) : Outcome
    ((core.result.Result Unit getrandom.error.Error) × Slice U8) :=
  match d.status with
  | .returned (.ok r) => .returned (.ok (r,(Array.to_slice_mut d.buffer).1))
  | .returned (.fail e) => .returned (.fail e)
  | .returned .div => .returned .div
  | .fault e => .fault e
  | .exhausted => .exhausted

def fill (slot : Slot) (driver : Slice U8 → State → Delivery)
    (buffer : Slice U8) : PV_EVH_NativeEntropyError.Fill := fun w =>
  let d := driver buffer w
  ⟨reply d,post slot d w,d.events⟩

theorem initialized_length (d : Delivery) : (encode d.buffer).length = 64 := by
  rw [encode,List.length_map,d.buffer.property]
  rfl

theorem retains_original_lookup (slot : Slot) (d : Delivery) (w : State)
    (h : w.frame.live.find? (sameKey slot.key) = some slot) :
    (post slot d w).frame.live.find? (sameKey slot.key) = some slot := h

theorem physical_buffer (slot : Slot) (d : Delivery) (w : State)
    (i : Nat) (hi : i < slot.initialized) :
    (post slot d w).memory (slot.address+i) = ((encode d.buffer)[i]?.getD 0).toNat :=
  PV_EVH_StackAdmission.write_inside slot (encode d.buffer) w i hi

theorem admitted_lookup (slot : Slot) (initial : PV_RJ4IDB.Bytes)
    (driver : Slice U8 → State → Delivery) (buffer : Slice U8) (w : State) :
    (fill slot driver buffer (PV_EVH_StackAdmission.enter slot initial w)).state.frame.live.find?
      (sameKey slot.key) = some slot :=
  PV_EVH_StackAdmission.enter_lookup slot initial w

theorem fault_prefix (slot : Slot) (driver : Slice U8 → State → Delivery)
    (buffer : Slice U8) (success : Slice U8 → Q PV_EVH_NativeEntropyError.Answer)
    (w : State) (fault : PV_EVH_Runtime.Fault)
    (hf : (driver buffer w).status = .fault fault) :
    PV_EVH_NativeEntropyError.afterFill slot.key (fill slot driver buffer) success w =
      ⟨.fault fault,post slot (driver buffer w) w,(driver buffer w).events⟩ := by
  simp only [PV_EVH_NativeEntropyError.afterFill,Bind.bind,PV_EVH_StackCleanup.bind,
    fill,reply,hf]

#print axioms initialized_length
#print axioms retains_original_lookup
#print axioms physical_buffer
#print axioms admitted_lookup
#print axioms fault_prefix
end PV_EVH_StackEntropyFill
