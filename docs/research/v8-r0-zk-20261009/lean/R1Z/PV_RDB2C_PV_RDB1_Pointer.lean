import Aeneas

/-! Sized pointer representation at the existing structural library boundary.
The intrinsic/raw-pointer interpretation is retained, not a Rust machine model.
NonNull is repr(transparent); as_ptr changes mutability and cast changes the
pointee type without changing the data address or provenance. No dereference,
allocation, exposure of provenance, or integer-to-pointer conversion occurs. -/
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_Pointer

structure Ptr (T P : Type) where
  provenance : P
  address : Nat
  deriving DecidableEq

structure NonNull (T P : Type) where
  pointer : Ptr T P

-- Transparent representation operations, with their source bindings checked
-- separately. Metadata is absent: every instantiated pointee here is Sized.
def asPtr {T P : Type} (p : NonNull T P) : Ptr T P := p.pointer

def rawCast {T U P : Type} (p : Ptr T P) : Ptr U P :=
  ⟨p.provenance, p.address⟩

def deployedCast {T U P : Type} (p : NonNull T P) : NonNull U P :=
  ⟨rawCast (asPtr p)⟩

def historicalCast {T U P : Type} (p : NonNull T P) : NonNull U P :=
  ⟨rawCast (asPtr p)⟩

theorem cast_complete {T U P W : Type} (p : NonNull T P) (world : W) :
    (ok (deployedCast (U := U) p, world) : Result (NonNull U P × W)) =
      ok (historicalCast p, world) := rfl

theorem cast_observation {T U P : Type} (p : NonNull T P) :
    (deployedCast (U := U) p).pointer.provenance = p.pointer.provenance ∧
    (deployedCast (U := U) p).pointer.address = p.pointer.address := ⟨rfl, rfl⟩

-- For a valid Vec, decrement selects an initialized slot strictly below
-- capacity. This also covers width=0: logical slot indices remain distinct.
theorem last_bounds (len cap : Nat) (nonempty : 0 < len) (fits : len ≤ cap) :
    len - 1 < len ∧ len - 1 < cap ∧ len - 1 + 1 ≤ cap := by omega

def offset {T P : Type} (p : Ptr T P) (count width : Nat) : Ptr T P :=
  ⟨p.provenance, p.address + count * width⟩

theorem offset_cast {T U P : Type} (p : NonNull T P) (count width : Nat) :
    offset (asPtr (deployedCast (U := U) p)) count width =
      rawCast (offset (asPtr p) count width) := rfl

theorem offset_bounds (base len cap width : Nat) (nonempty : 0 < len)
    (fits : len ≤ cap) :
    base + (len - 1) * width ≤ base + len * width ∧
    base + len * width ≤ base + cap * width := by
  constructor
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right width (by omega)) base
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right width fits) base

theorem offset_zst {T P : Type} (p : Ptr T P) (count : Nat) :
    offset p count 0 = p := by cases p; simp only [offset, Nat.mul_zero, Nat.add_zero]

-- No address wrap on the initialized prefix if the retained buffer invariant
-- says the end of the allocation is representable. No such fact is assumed
-- for arbitrary, possibly invalid raw pointers.
theorem no_wrap (base len cap width maxAddr : Nat) (hn : 0 < len)
    (hc : len ≤ cap) (endFits : base + cap * width ≤ maxAddr) :
    base + (len - 1) * width ≤ maxAddr :=
  le_trans (offset_bounds base len cap width hn hc).1
    (le_trans (offset_bounds base len cap width hn hc).2 endFits)

#print axioms cast_complete
#print axioms cast_observation
#print axioms last_bounds
#print axioms offset_cast
#print axioms offset_bounds
#print axioms offset_zst
#print axioms no_wrap
end R1Z.PV_RDB1_Pointer
