import S6SliceRecomposeV1
set_option autoImplicit false
namespace AspisS6SliceFrame

theorem slice_two {T : Type} (xs : List T) (start : Nat)
    (bound : start+2≤xs.length) :
    List.slice start (start+2) xs=[xs[start+0]'(by omega),xs[start+1]'(by omega)] := by
  apply List.ext_getElem
  · simp [List.slice,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have hin : i<2 := by simpa using hj
    interval_cases i <;> simp [List.slice]

#print axioms slice_two

theorem slice_eight {T : Type} (xs : List T) (start : Nat)
    (bound : start+8≤xs.length) :
    List.slice start (start+8) xs=[xs[start+0]'(by omega),xs[start+1]'(by omega),xs[start+2]'(by omega),xs[start+3]'(by omega),xs[start+4]'(by omega),xs[start+5]'(by omega),xs[start+6]'(by omega),xs[start+7]'(by omega)] := by
  apply List.ext_getElem
  · simp [List.slice,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have hin : i<8 := by simpa using hj
    interval_cases i <;> simp [List.slice]

#print axioms slice_eight
end AspisS6SliceFrame
