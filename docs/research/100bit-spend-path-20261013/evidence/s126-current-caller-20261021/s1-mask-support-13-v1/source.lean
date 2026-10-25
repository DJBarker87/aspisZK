import Aeneas.Std.Array.Array

/-! Draft only: symbolic pointwise bridge for the two coefficient-array population loops.
    The source and generated function hashes are recorded in the accompanying note. -/

namespace AspisR1.ExtractedMaskCoefficientArray

open Aeneas Aeneas.Std

/-- The update API already exposes a refinement to the functional `Array.set`. -/
theorem update_refines_set {α : Type} {n : Usize} (v : Array α n)
    (i : Usize) (x : α) (hbound : i.val < v.length) :
    v.update i x ⦃ nv => nv = v.set i x ⦄ :=
  Array.update_spec v i x hbound

/-- At the updated coefficient, the resulting functional array contains `x`. -/
theorem set_at_updated_index {α : Type} {n : Usize} (v : Array α n)
    (i : Usize) (x : α) (h : i.val < (v.set i x).length) :
    (v.set i x)[i]'h = x :=
  Array.getElem_set_eq v i x h

/-- A write to a different coefficient preserves the previous cell. -/
theorem set_preserves_other_index {α : Type} {n : Usize} (v : Array α n)
    (i j : Usize) (x : α) (hj : j.val < (v.set i x).length)
    (hij : i ≠ j) :
    (v.set i x)[j]'hj = v[j]'(by simpa using hj) :=
  Array.getElem_set_neq v i j x (by simpa using hj) hij

/-- First loop's exact exponent schedule. For indices 0..13 it is `2*j`,
    followed by the exceptional source entries 13 and 25. -/
def c1Exponent (j : Fin 16) : Fin 27 :=
  if h : j.val < 14 then ⟨2 * j.val, by omega⟩
  else if j.val = 14 then ⟨13, by omega⟩ else ⟨25, by omega⟩

/-- Second loop's exact exponent schedule. Indices 0..5 map to `2*j+1`;
    indices 6..9 map to `2*j+3`. -/
def maskExponent (j : Fin 10) : Fin 27 :=
  if h : j.val < 6 then ⟨2 * j.val + 1, by omega⟩
  else ⟨2 * j.val + 3, by omega⟩

/-- Intended loop-0 invariant after `k` successful iterations: the processed
    source cells occupy their table exponents with their `column mod 4` basis
    transform, and all other cells retain the initial array value.  `value`
    abstracts the exact `mul_tower_basis` result to keep this invariant
    independent of field-arithmetic proofs. -/
def Loop0Invariant {α : Type} (initial current : Fin 27 → α)
    (source : Fin 16 → α) (value : α → Fin 4 → α) (k : Nat) : Prop :=
  (∀ j : Fin 16, j.val < k →
      current (c1Exponent j) = value (source j) ⟨j.val % 4, by omega⟩) ∧
  (∀ e : Fin 27,
      (∀ j : Fin 16, j.val < k → c1Exponent j ≠ e) →
      current e = initial e)

/-- Intended loop-1 invariant after `k` successful iterations, starting from
    the completed loop-0 array. The odd exponent schedule is disjoint from the
    even/exceptional loop-0 schedule, so its non-written cells remain exactly
    the loop-0 result. -/
def Loop1Invariant {α : Type} (after0 current : Fin 27 → α)
    (source : Fin 10 → α) (value : α → Fin 4 → α) (k : Nat) : Prop :=
  (∀ j : Fin 10, j.val < k →
      current (maskExponent j) = value (source j) ⟨j.val % 4, by omega⟩) ∧
  (∀ e : Fin 27,
      (∀ j : Fin 10, j.val < k → maskExponent j ≠ e) →
      current e = after0 e)

#print axioms update_refines_set
#print axioms set_at_updated_index
#print axioms set_preserves_other_index

end AspisR1.ExtractedMaskCoefficientArray
