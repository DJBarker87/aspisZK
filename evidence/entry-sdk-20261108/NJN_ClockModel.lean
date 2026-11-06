import NJH_SyscallLaws
set_option autoImplicit false
namespace NJN_ClockModel
/-- All fields of the concrete Clock, not a slot-only successful projection. -/
structure Clock where
  slot : Nat
  epochStartTimestamp : Int
  epoch : Nat
  leaderScheduleEpoch : Nat
  unixTimestamp : Int
  deriving DecidableEq
/-- Exact From<u64> image. Builtin 15 denotes BorshIoError("Unknown"). -/
inductive ProgramError where
  | custom (code : Nat)
  | builtin (tag : Nat)
  deriving DecidableEq

def convert (status : Nat) : ProgramError :=
  if status = 2^32 then .custom 0
  else if status % 2^32 = 0 ∧ 2 ≤ status / 2^32 ∧ status / 2^32 ≤ 26 then
    .builtin (status / 2^32)
  else .custom (status % 2^32)

def get (status : Nat) (output : Clock) : Except ProgramError Clock :=
  if status = 0 then .ok output else .error (convert status)

structure Output (Frame : Type) where
  status : Nat
  region : Clock
  result : Except ProgramError Clock
  frame : Frame

def invoke {Frame : Type} (frame : Frame) (status : Nat) (output : Clock) : Output Frame :=
  ⟨status, output, get status output, frame⟩

theorem success (output : Clock) : get 0 output = .ok output := by simp [get]
theorem failure (status : Nat) (output : Clock) (ne : status ≠ 0) :
    get status output = .error (convert status) := by simp [get,ne]
theorem custom_zero : convert (2^32) = .custom 0 := by simp [convert]
theorem custom_other (status : Nat) (nz : status ≠ 2^32)
    (other : ¬ (status % 2^32 = 0 ∧ 2 ≤ status / 2^32 ∧ status / 2^32 ≤ 26)) :
    convert status = .custom (status % 2^32) := by rw [convert, if_neg nz, if_neg other]
theorem builtin (status : Nat) (nz : status ≠ 2^32)
    (domain : status % 2^32 = 0 ∧ 2 ≤ status / 2^32 ∧ status / 2^32 ≤ 26) :
    convert status = .builtin (status / 2^32) := by rw [convert, if_neg nz, if_pos domain]
theorem region_frame {Frame : Type} (frame : Frame) (status : Nat) (output : Clock) :
    (invoke frame status output).region = output ∧
    (invoke frame status output).status = status ∧
    (invoke frame status output).frame = frame := ⟨rfl,rfl,rfl⟩
/-- Slot binding is used only after SDK success, never as an assumed success. -/
theorem slot_binding (status bankSlot : Nat) (output returned : Clock)
    (binding : status = 0 → output.slot = bankSlot)
    (success : get status output = .ok returned) : returned.slot = bankSlot := by
  by_cases eq : status = 0
  · simp [get,eq] at success
    subst returned
    exact binding eq
  · simp [get,eq] at success
#print axioms success
#print axioms failure
#print axioms custom_zero
#print axioms custom_other
#print axioms builtin
#print axioms region_frame
#print axioms slot_binding
end NJN_ClockModel
