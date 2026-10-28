import R1Z.PV_RDB2C_Base_ConstructorEffects

/-! Whole-allocation owned copy/fill semantics. For the reached safe slice
copies, the source and output are separate borrowed allocations and the
destination slice is the entire output. Native intrinsics are related to
this explicit snapshot semantics by the deployed structural source gate. -/
namespace R1Z.PV_RDB2_CopyEffects
set_option autoImplicit false
open Aeneas Aeneas.Std Result

abbrev Heap (T : Type) := Nat → List T
def write {T : Type} (heap : Heap T) (dst : Nat) (bytes : List T) : Heap T :=
  fun location => if location = dst then bytes else heap location

def copy {T : Type} (heap : Heap T) (src dst : Nat) : Result (Heap T) :=
  if (heap src).length = (heap dst).length then ok (write heap dst (heap src))
  else fail .panic

def fill {T : Type} (heap : Heap T) (dst n : Nat) (value : T) : Result (Heap T) :=
  if (heap dst).length = n then ok (write heap dst (List.replicate n value))
  else fail .panic

/-- Copy a checked source subrange into the complete destination output. -/
def copyRange {T : Type} (heap : Heap T) (src start dst : Nat) : Result (Heap T) :=
  if start+(heap dst).length ≤ (heap src).length then
    ok (write heap dst (((heap src).drop start).take (heap dst).length))
  else fail .panic

theorem range_complete {T : Type} (heap : Heap T) (src start dst : Nat)
    (bounds : start+(heap dst).length ≤ (heap src).length) :
    copyRange heap src start dst =
      ok (write heap dst (((heap src).drop start).take (heap dst).length)) := if_pos bounds

theorem range_rejected {T : Type} (heap : Heap T) (src start dst : Nat)
    (bounds : ¬start+(heap dst).length ≤ (heap src).length) :
    copyRange heap src start dst = fail .panic := if_neg bounds

theorem copy_complete {T : Type} (heap : Heap T) (src dst : Nat)
    (lengths : (heap src).length = (heap dst).length) :
    copy heap src dst = ok (write heap dst (heap src)) := if_pos lengths

theorem copy_rejected {T : Type} (heap : Heap T) (src dst : Nat)
    (lengths : (heap src).length ≠ (heap dst).length) :
    copy heap src dst = fail .panic := if_neg lengths

theorem copied_destination {T : Type} (heap : Heap T) (src dst : Nat) :
    write heap dst (heap src) dst = heap src := if_pos rfl

theorem copy_frame {T : Type} (heap : Heap T) (src dst location : Nat)
    (different : location ≠ dst) :
    write heap dst (heap src) location = heap location := if_neg different

theorem source_preserved {T : Type} (heap : Heap T) (src dst : Nat)
    (disjoint : src ≠ dst) : write heap dst (heap src) src = heap src :=
  copy_frame heap src dst src disjoint

theorem destination_length {T : Type} (heap : Heap T) (src dst : Nat)
    (lengths : (heap src).length = (heap dst).length) :
    (write heap dst (heap src) dst).length = (heap dst).length := by
  rw [copied_destination,lengths]

theorem fill_complete {T : Type} (heap : Heap T) (dst n : Nat) (value : T)
    (length : (heap dst).length = n) :
    fill heap dst n value = ok (write heap dst (List.replicate n value)) := if_pos length

theorem fill_cell {T : Type} (heap : Heap T) (dst n i : Nat) (value : T)
    (active : i < n) :
    (write heap dst (List.replicate n value) dst)[i]? = some value := by
  simp only [write,↓reduceIte,List.getElem?_replicate]
  exact if_pos active

/-- Every MaybeUninit byte is initialized before the output is viewed as
an array of bytes; no uninitialized value is silently decoded as zero. -/
theorem initialized32 (heap : Heap (Option U8)) (dst i : Nat) (active : i < 32) :
    (write heap dst (List.replicate 32 (some 0#u8)) dst)[i]? = some (some 0#u8) :=
  fill_cell heap dst 32 i (some 0#u8) active

#print axioms copy_complete
#print axioms range_complete
#print axioms range_rejected
#print axioms copy_rejected
#print axioms copied_destination
#print axioms copy_frame
#print axioms source_preserved
#print axioms destination_length
#print axioms fill_complete
#print axioms fill_cell
#print axioms initialized32
end R1Z.PV_RDB2_CopyEffects
