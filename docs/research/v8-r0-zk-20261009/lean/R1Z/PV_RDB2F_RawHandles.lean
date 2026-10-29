import R1Z.PV_RDB2F_ArrayHandles
import R1Z.PV_RDB2E_PointerOffsets
namespace R1Z.PV_RDB2F_RawHandles
open Aeneas Aeneas.Std Result PV_RDB2F_Iterator
set_option autoImplicit false
abbrev Memory := Nat → Option U32
abbrev address := PV_RDB2E_PointerOffsets.address
/-- The live allocation, including all eight words, rather than a captured snapshot. -/
def Represents (mem : Memory) (base : Nat) (current : Words) : Prop :=
  ∀ j : Usize, j.val < 8 → mem (address base j.val) = current.val[j.val]?
def store (mem : Memory) (ptr : Nat) (value : U32) : Memory :=
  fun a => if a = ptr then some value else mem a

theorem address_offset (base i : Nat) : (address base i-base)/4=i := by
  unfold address PV_RDB2E_PointerOffsets.address
  omega

theorem store_read (mem : Memory) (ptr : Nat) (value : U32) :
    store mem ptr value ptr = some value := by simp [store]

theorem store_frame (mem : Memory) (ptr a : Nat) (value : U32) (h : a≠ptr) :
    store mem ptr value a=mem a := by simp [store,h]

/-- Dereferencing the raw returned reference restores exactly the current array.
All other addresses, and therefore other allocations, are framed. -/
theorem current_array_store (mem : Memory) (base : Nat) (current : Words)
    (i : Usize) (value : U32) (rep : Represents mem base current) (bound : i.val<8) :
    Represents (store mem (address base i.val) value) base (current.set i value) := by
  intro j hj
  by_cases e : j.val=i.val
  · have ja : j=i := by exact Subtype.ext e
    subst j
    rw [store_read,PV_RDB2F_ArrayHandles.readback current i value bound]
  · rw [store_frame mem _ _ value ((PV_RDB2E_PointerOffsets.injective base _ _).not.mpr e),
        PV_RDB2F_ArrayHandles.frame current i j value e]
    exact rep j hj

/-- A borrow created earlier carries its address; stores do not restore stale words. -/
theorem borrowed_address_current (before current : Words) (mem : Memory) (base : Nat)
    (i : Usize) (value : U32) (rep : Represents mem base current) (bound : i.val<8) :
    (fun (_ : Words) => Represents (store mem (address base i.val) value) base
      (current.set i value)) before := current_array_store mem base current i value rep bound

#print axioms address_offset
#print axioms store_read
#print axioms store_frame
#print axioms current_array_store
#print axioms borrowed_address_current
end R1Z.PV_RDB2F_RawHandles
