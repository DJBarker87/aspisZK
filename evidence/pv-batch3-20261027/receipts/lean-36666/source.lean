import Aeneas.Std
namespace PV_B3_MaskUnion
set_option autoImplicit false

-- OR is a set operation: source sorting/deduplication is observationally
-- irrelevant for the mask, independently of endpoint validation and errors.
def union : List Nat → Nat
  | [] => 0
  | x :: xs => x ||| union xs

theorem bit (xs : List Nat) (j : Nat) :
    Nat.testBit (union xs) j = true ↔ ∃ x ∈ xs, Nat.testBit x j = true := by
  induction xs with
  | nil => simp [union]
  | cons x xs ih => simp [union, Nat.testBit_or, ih]

theorem ext (xs ys : List Nat) (h : ∀ x, x ∈ xs ↔ x ∈ ys) : union xs = union ys := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [bit, bit]
  constructor
  · rintro ⟨x, hx, hb⟩; exact ⟨x, (h x).mp hx, hb⟩
  · rintro ⟨x, hx, hb⟩; exact ⟨x, (h x).mpr hx, hb⟩

def rowMask (block row : Nat) : Nat :=
  if row / 16 = block then 2^(row % 16) else 0

def blockMask (rows : List Nat) (block : Nat) : Nat := union (rows.map (rowMask block))

theorem block_ext (xs ys : List Nat) (h : ∀ row, row ∈ xs ↔ row ∈ ys) (b : Nat) :
    blockMask xs b = blockMask ys b := by
  apply ext
  intro x
  simp only [List.mem_map]
  constructor
  · rintro ⟨r, hr, hv⟩; exact ⟨r, (h r).mp hr, hv⟩
  · rintro ⟨r, hr, hv⟩; exact ⟨r, (h r).mpr hr, hv⟩

theorem dedup (xs : List Nat) (b : Nat) : blockMask xs.eraseDups b = blockMask xs b := by
  apply block_ext
  intro r
  exact List.mem_eraseDups

#print axioms union
#print axioms bit
#print axioms ext
#print axioms rowMask
#print axioms blockMask
#print axioms block_ext
#print axioms dedup
end PV_B3_MaskUnion
