import NBE_BatchDomains

set_option autoImplicit false
namespace AspisR1.NBE_KeyLoop

/-- Pointwise denotation of the single native key-array write. The arbitrary
coordinate frame is checked by NBE_key; no whole-loop equality is assumed. -/
def write {α : Type} (word state : Nat → α) (cursor : Nat) : Nat → α :=
  fun k => if k = cursor then word cursor else state k

/-- Forward source order: update this cell, then advance the cursor. -/
def fill {α : Type} (word : Nat → α) : Nat → Nat → (Nat → α) → (Nat → α)
  | 0, _, state => state
  | fuel+1, cursor, state => fill word fuel (cursor+1) (write word state cursor)

/-- All coordinates, including the entire untouched suffix. -/
theorem fill_values {α : Type} (word initial : Nat → α) (fuel cursor k : Nat) :
    fill word fuel cursor initial k =
      if cursor ≤ k ∧ k < cursor+fuel then word k else initial k := by
  induction fuel generalizing cursor initial with
  | zero => simp [fill]
  | succ fuel ih =>
    rw [fill, ih]
    by_cases hit : k = cursor
    · subst k
      rw [if_neg (by omega), write, if_pos rfl, if_pos (by omega)]
    · by_cases later : cursor+1 ≤ k ∧ k < cursor+1+fuel
      · rw [if_pos later, if_pos (by omega)]
      · rw [if_neg later, write, if_neg hit, if_neg (by omega)]

/-- Each reached induction step satisfies the same bounds as the native
one-iteration gate, derived from the actual split, for BOTH transactions. -/
theorem reached_domain (batch : Aeneas.Std.Usize) (cursor : Nat)
    (active : cursor < (Port4B_TreeCuts.count batch).val) :
    cursor < 16 ∧ cursor < 256 ∧
    (Port4B_TreeCuts.lo batch).val + cursor < 22 :=
  NBE_BatchDomains.key_domain batch cursor active

#print axioms fill_values
#print axioms reached_domain
end AspisR1.NBE_KeyLoop
