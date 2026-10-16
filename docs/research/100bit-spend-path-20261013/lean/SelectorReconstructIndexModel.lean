import R0P.Value

/-! Symbolic equation for the proposed candidate's explicit descending-index
reconstruction loop. The only fixed expansion is its ten-symbol old model
closed form; no generated loop or opaque Rev.fold is unfolded here. -/
set_option autoImplicit false
namespace AspisR1.SelectorReconstructIndexModel

variable {K : Type} [Field K]

def reconstructIndexed (view : Nat → K) : Nat → K → K
  | 0, acc => acc
  | n + 1, acc => reconstructIndexed view n (acc + acc + view n)

theorem reconstructIndexed_nine_eq_valueReconstruct10 (view : Nat → K) :
    reconstructIndexed view 9 (view 9) =
      R0P.valueReconstruct10 (fun i : Fin 16 => view i.val) := by
  rw [R0P.value_reconstruct10_eq]
  simp only [reconstructIndexed]
  norm_num
  ring

#print axioms reconstructIndexed_nine_eq_valueReconstruct10
end AspisR1.SelectorReconstructIndexModel
