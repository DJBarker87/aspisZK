import RPt_JFq_Range
set_option autoImplicit false
namespace AspisR1.JHn_Ranges
/-- Adjacent ranges compose without inspecting their elements. -/
theorem adjacent {A : Type} (xs : List A) (off n m : Nat) :
    (xs.drop off).take n ++ (xs.drop (off+n)).take m =
      (xs.drop off).take (n+m) := by
  rw [←List.drop_drop]
  exact List.take_add.symm
#print axioms adjacent
end AspisR1.JHn_Ranges
