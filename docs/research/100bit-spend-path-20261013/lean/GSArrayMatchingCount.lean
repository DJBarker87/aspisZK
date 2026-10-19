import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

open CompPoly
open CompPoly.CBivariate
open CompPoly.GuruswamiSudan

namespace AspisWide.GSArrayMatchingCount

private theorem matching_count_eq_filter_length {F : Type*} [Semiring F] [BEq F]
    (points : Array (F × F)) (p : CPolynomial F) :
    matchingPointCount points p =
      (points.toList.filter
        (fun point ↦ CPolynomial.eval point.1 p == point.2)).length := by
  cases points with
  | mk data =>
      unfold matchingPointCount
      let pred : F × F → Bool := fun point ↦ CPolynomial.eval point.1 p == point.2
      let step : Nat → F × F → Nat := fun count point =>
        if pred point then count + 1 else count
      have hfold : ∀ (xs : List (F × F)) acc,
          xs.foldl step acc = acc + (xs.filter pred).length := by
        intro xs
        induction xs with
        | nil => intro acc; simp
        | cons point tail ih =>
            intro acc
            simp only [List.foldl_cons]
            rw [ih]
            by_cases h : pred point = true
            · simp [step, pred, h, Nat.add_assoc, Nat.add_comm]
            · have hfalse : pred point = false := by
                cases hp : pred point <;> simp_all
              simp [step, pred, hfalse, Nat.add_comm]
      simpa [pred, step] using hfold data 0

private theorem countP_ofFn_eq_sum {α : Type*} (n : Nat) (f : Fin n → α)
    (b : α → Bool) :
    (List.ofFn f).countP b = ∑ i : Fin n, if b (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
      simp [add_comm]

theorem matching_count_ofFn {F : Type*} [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] (n : Nat) (points : Fin n → F × F)
    (p : CPolynomial F) :
    matchingPointCount (Array.ofFn points) p =
      (Finset.univ.filter fun i : Fin n =>
        CPolynomial.eval (points i).1 p = (points i).2).card := by
  rw [matching_count_eq_filter_length]
  classical
  rw [← List.countP_eq_length_filter, Array.toList_ofFn]
  rw [countP_ofFn_eq_sum]
  calc
    (∑ i : Fin n, if CPolynomial.eval (points i).1 p == (points i).2 then 1 else 0) =
        ∑ i ∈ Finset.univ,
          if CPolynomial.eval (points i).1 p = (points i).2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [beq_iff_eq]
    _ = (Finset.univ.filter fun i : Fin n =>
          CPolynomial.eval (points i).1 p = (points i).2).card := by
      rw [Finset.sum_boole]
      simp

#print axioms matching_count_ofFn

end AspisWide.GSArrayMatchingCount
