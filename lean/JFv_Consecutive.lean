import JFv_CanonicalSlice
set_option autoImplicit false
namespace AspisR1.JFv_Consecutive

theorem slice {α : Type} (xs : List α) (start n : Nat) (bound : start+n ≤ xs.length) :
    List.ofFn (fun i : Fin n => xs[start+i.val]'(by omega)) = (xs.drop start).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,List.getElem_drop]

#print axioms slice
end AspisR1.JFv_Consecutive
