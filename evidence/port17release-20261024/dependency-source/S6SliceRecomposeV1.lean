import Aeneas
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisS6SliceFrame

/-- Consecutive source slice frames telescope without enumerating their bytes. -/
theorem take_append_slice {T : Type} (xs : List T) (start stop : Nat)
    (h : start≤stop) :
    xs.take start++List.slice start stop xs=xs.take stop := by
  unfold List.slice
  rw [←List.take_add]
  congr 1
  omega

theorem slice_four {T : Type} (xs : List T) (start : Nat)
    (h : start+4≤xs.length) :
    List.slice start (start+4) xs=
      [xs[start]'(by omega),xs[start+1]'(by omega),
       xs[start+2]'(by omega),xs[start+3]'(by omega)] := by
  apply List.ext_getElem
  · simp [List.slice,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have hi4 : i<4 := by
      simp only [List.length_cons,List.length_nil] at hj
      exact hj
    interval_cases i <;> simp [List.slice]

theorem header_eight {T : Type} (xs : List T) (h : 8≤xs.length) :
    xs.take 8=xs.take 4++
      [xs[4]'(by omega),xs[5]'(by omega),xs[6]'(by omega),xs[7]'(by omega)] := by
  rw [←take_append_slice xs 4 8 (by decide)]
  rw [slice_four xs 4 (by omega)]

#print axioms take_append_slice
#print axioms slice_four
#print axioms header_eight
end AspisS6SliceFrame
