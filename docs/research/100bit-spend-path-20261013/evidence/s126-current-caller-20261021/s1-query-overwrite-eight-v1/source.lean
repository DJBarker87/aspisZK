import Aeneas.Std
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS1QueryOverwriteEight

def writeEight {A : Type} (a : Array A 8#usize) (x0 x1 x2 x3 x4 x5 x6 x7 : A) : Array A 8#usize :=
  ((((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
    4#usize x4).set 5#usize x5).set 6#usize x6).set 7#usize x7)

/-- Symbolic eight-cell overwrite. No hash/field computation or large
recurrence is evaluated, and the original array need not be zero. -/
theorem writeEight_eq_make {A : Type} (a : Array A 8#usize) (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    writeEight a x0 x1 x2 x3 x4 x5 x6 x7=Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,x7] := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [writeEight,Array.set_val_eq,List.length_set,Array.make]
    exact a.property
  · intro i left right
    have bound : i<8 := by
      simpa only [writeEight,Array.set_val_eq,List.length_set,a.property] using left
    interval_cases i <;> simp [writeEight,Array.set_val_eq,Array.make]

#print axioms writeEight_eq_make
end AspisS1QueryOverwriteEight
