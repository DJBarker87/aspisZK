import AspisV8R17.IndexSchedule
import Mathlib.Tactic.Ring

/-! Generic mass preservation for the weighted, finite index schedule. -/
set_option autoImplicit false
namespace AspisV8R19.R774WeightedScheduleMass

open AspisV8R17

theorem weighted_index_loop_mass
    {F : Type*} [CommRing F] (half : F) (hhalf : half + half = 1)
    (fuel row bit : Nat) (scale : F) (edges : List (Nat × F))
    (h : weightedIndexLoop half fuel row bit scale = some edges) :
    (edges.map Prod.snd).sum = scale := by
  induction fuel generalizing row bit scale edges with
  | zero => simp [weightedIndexLoop] at h
  | succ fuel ih =>
      simp only [weightedIndexLoop]
      split
      · rename_i hbit
        simp only [hbit, ↓reduceIte] at h
        cases hrest : weightedIndexLoop half fuel (row ^^^ 2 ^ bit) (bit + 1)
            (scale * half) with
        | none => simp [hrest] at h
        | some rest =>
            simp only [hrest, Option.map_some] at h
            cases h
            have hmass := ih (row ^^^ 2 ^ bit) (bit + 1) (scale * half) rest hrest
            simp only [List.map_cons, List.sum_cons, Prod.snd, hmass]
            calc
              scale * half + scale * half = scale * (half + half) := by ring
              _ = scale := by rw [hhalf, mul_one]
      · rename_i hbit
        simp only [hbit, ↓reduceIte] at h
        cases h
        simp

theorem weighted_index_loop_constant_mass
    {F : Type*} [CommRing F] (half : F) (hhalf : half + half = 1)
    (fuel row bit : Nat) (scale : F) (edges : List (Nat × F))
    (h : weightedIndexLoop half fuel row bit scale = some edges)
    (w : Nat → F) (C : F) (hw : ∀ e ∈ edges, w e.1 = C) :
    (edges.map (fun e => e.2 * w e.1)).sum = scale * C := by
  have hmap : edges.map (fun e => e.2 * w e.1) =
      edges.map (fun e => e.2 * C) := by
    apply List.map_congr_left
    intro e he
    rw [hw e he]
  rw [hmap]
  have hsum : ∀ xs : List (Nat × F),
      (xs.map (fun e => e.2 * C)).sum = (xs.map Prod.snd).sum * C := by
    intro xs
    induction xs with
    | nil => simp
    | cons e xs ih => simp only [List.map_cons, List.sum_cons, Prod.snd, ih, add_mul]
  rw [hsum, weighted_index_loop_mass half hhalf fuel row bit scale edges h]

#print axioms weighted_index_loop_mass
#print axioms weighted_index_loop_constant_mass

end AspisV8R19.R774WeightedScheduleMass
