import KMX_CopyMeaning
set_option autoImplicit false
namespace NBU_CopyWindows
/-- Arbitrary-offset value view of the prescribed KMX indexed copy loop. -/
def window {α : Type} (dst : Nat → α) (bytes : Nat → α)
    (start count : Nat) : Nat → α :=
  KMX_CopyMeaning.loop (fun i => bytes (i-start)) dst start count

theorem window_spec {α : Type} (dst bytes : Nat → α) (start count j : Nat) :
    window dst bytes start count j =
      if start ≤ j ∧ j < start+count then bytes (j-start) else dst j :=
  KMX_CopyMeaning.loop_spec _ _ _ _ _

/-- A later disjoint row cannot change a byte already written by this row. -/
theorem disjoint {α : Type} (dst first second : Nat → α)
    (a na b nb j : Nat) (in_first : a ≤ j ∧ j < a+na)
    (separate : a+na ≤ b ∨ b+nb ≤ a) :
    window (window dst first a na) second b nb j = first (j-a) := by
  rw [window_spec, if_neg (by omega), window_spec, if_pos in_first]

/-- Sequential rows. Source values remain arbitrary, including every byte. -/
def rows {α : Type} (src : Nat → Nat → α) (dst : Nat → α)
    (base width : Nat) : Nat → Nat → α
  | 0 => dst
  | n+1 => window (rows src dst base width n) (src n) (base+width*n) width

/-- Induction lifts one native arbitrary-prestate row to all rows and frame. -/
theorem rows_spec {α : Type} (src : Nat → Nat → α) (dst : Nat → α)
    (base width count j : Nat) (positive : 0 < width) :
    rows src dst base width count j =
      if base ≤ j ∧ j < base+width*count
      then src ((j-base)/width) ((j-base)%width) else dst j := by
  induction count with
  | zero => simp [rows]; omega
  | succ n ih =>
    rw [rows, window_spec]
    by_cases last : base+width*n ≤ j ∧ j < base+width*n+width
    · rw [if_pos last]
      have whole : base ≤ j ∧ j < base+width*(n+1) := by omega
      rw [if_pos whole]
      have eqdiv : (j-base)/width = n := by omega
      have eqmod : (j-base)%width = j-(base+width*n) := by omega
      rw [eqdiv, eqmod]
    · rw [if_neg last, ih]
      have equivalent : (base ≤ j ∧ j < base+width*n) ↔
          (base ≤ j ∧ j < base+width*(n+1)) := by omega
      simp only [equivalent]

#print axioms window_spec
#print axioms disjoint
#print axioms rows_spec
end NBU_CopyWindows
