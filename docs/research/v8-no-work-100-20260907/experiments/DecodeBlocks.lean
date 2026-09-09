import Mathlib.Tactic

namespace AspisV8.DecodeBlocks

-- State after writing b complete eight-limb blocks into the flat output.
-- The inner block's value function is arbitrary: byte unpacking is unchanged.
def overwritten {A : Type*} (initial : Nat → A) (values : Nat → Nat → A) :
    Nat → Nat → A
  | 0 => initial
  | b+1 => fun i => if i/8=b then values b (i%8) else overwritten initial values b i

theorem overwritten_eq_direct {A : Type*} (initial : Nat → A)
    (values : Nat → Nat → A) (b i : Nat) (hi : i < 8*b) :
    overwritten initial values b i = values (i/8) (i%8) := by
  induction b with
  | zero => omega
  | succ b ih =>
    simp only [overwritten]
    split_ifs with h
    · rw [h]
    · apply ih
      omega

theorem initial_fill_irrelevant {A : Type*} (a c : Nat → A)
    (values : Nat → Nat → A) (b i : Nat) (hi : i < 8*b) :
    overwritten a values b i = overwritten c values b i := by
  rw [overwritten_eq_direct a values b i hi,overwritten_eq_direct c values b i hi]

theorem flatten_indices {b i : Nat} (hi : i < 8*b) :
    i/8 < b ∧ i%8 < 8 ∧ 8*(i/8)+i%8=i := by omega

-- Both rejection scans visit exactly the same cells, for any predicate.
theorem checks_equivalent (b : Nat) (values : Nat → Nat → Nat) (ok : Nat → Prop) :
    (∀ i, i < 8*b → ok (values (i/8) (i%8))) ↔
    (∀ row, row < b → ∀ col, col < 8 → ok (values row col)) := by
  constructor
  · intro h row hr col hc
    have hi : 8*row+col < 8*b := by omega
    have hd : (8*row+col)/8=row := by omega
    have hm : (8*row+col)%8=col := by omega
    simpa only [hd,hm] using h (8*row+col) hi
  · intro h i hi
    exact h (i/8) (by omega) (i%8) (by omega)

-- Literal four load starts stay inside each checked 31-byte input block.
theorem load_bounds (b row start : Nat) (hr : row < b)
    (hs : start ∈ [0,8,16,23]) :
    start+8 ≤ 31 ∧ 31*row+start+8 ≤ 31*b := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with h|h|h|h <;> subst start <;> omega

theorem selected_index_ranges (b row : Nat) (hb : b=13 ∨ b=6) (hr : row < b) :
    31*(row+1) ≤ 403 ∧ 8*(row+1) ≤ 104 := by omega

#print axioms overwritten_eq_direct
#print axioms initial_fill_irrelevant
#print axioms flatten_indices
#print axioms checks_equivalent
#print axioms load_bounds
#print axioms selected_index_ranges
end AspisV8.DecodeBlocks
