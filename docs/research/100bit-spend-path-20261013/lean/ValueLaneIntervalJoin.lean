import ValueLanePackedComposition

/-! Zero-padded interval concatenation for the two value-family source arrays.
This is generic finite-vector algebra; it permits the two source packing calls
to be identified with one 35-residual value-family interval. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneIntervalJoin

/-- Concatenation preserves the original coordinates of each finite vector. -/
def appendVector {K : Type} {n m : Nat} (a : Fin n → K) (b : Fin m → K) : Fin (n+m) → K :=
  fun i => if h : i.val < n then a ⟨i.val, h⟩ else b ⟨i.val-n, by omega⟩

def selectVector {K : Type} [Zero K] {n : Nat}
    (start : Nat) (a : Fin n → K) (index : Nat) : K :=
  if h : start ≤ index ∧ index < start+n then a ⟨index-start, by omega⟩ else 0

theorem selectVector_append {K : Type} [AddZeroClass K] {n m : Nat}
    (start index : Nat) (a : Fin n → K) (b : Fin m → K) :
    selectVector start (appendVector a b) index =
      selectVector start a index + selectVector (start+n) b index := by
  by_cases hbefore : index < start
  · unfold selectVector
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), zero_add]
  · by_cases hfirst : index < start+n
    · unfold selectVector
      rw [dif_pos (by omega), dif_pos (by omega), dif_neg (by omega), add_zero]
      unfold appendVector
      rw [dif_pos (by change index-start < n; omega)]
    · by_cases hsecond : index < start+(n+m)
      · unfold selectVector
        rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega), zero_add]
        unfold appendVector
        rw [dif_neg (by change ¬ index-start < n; omega)]
        congr 1
        apply Fin.ext
        change (index-start)-n = index-(start+n)
        omega
      · unfold selectVector
        rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), zero_add]

theorem pack4_selectVector_append {K : Type} [Field K] {F : Subfield K}
    (B : R0P.PackBasis F) {n m : Nat} (start group : Nat)
    (a : Fin n → K) (b : Fin m → K) :
    R0P.pack4 B (fun j => selectVector start (appendVector a b) (4*group+j.val)) =
      R0P.pack4 B (fun j => selectVector start a (4*group+j.val)) +
      R0P.pack4 B (fun j => selectVector (start+n) b (4*group+j.val)) := by
  rw [← AspisR1.ValueLanePackedComposition.pack_add]
  congr 1
  funext j
  exact selectVector_append start (4*group+j.val) a b

#print axioms selectVector_append
#print axioms pack4_selectVector_append
end AspisR1.ValueLaneIntervalJoin
