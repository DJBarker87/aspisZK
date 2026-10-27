import RPv_FJn_CopyFullValue
set_option autoImplicit false
namespace AspisR1.FJn_FoldMap
/-- Symbolic fold transport; list length and contents are never evaluated. -/
theorem value {I K L : Type} (f : K → L) (xs : List I)
    (step : K → I → K) (step' : L → I → L)
    (commutes : ∀ a i,f (step a i)=step' (f a) i) (seed : K) :
    f (xs.foldl step seed)=xs.foldl step' (f seed) := by
  induction xs generalizing seed with
  | nil => rfl
  | cons i xs ih => rw [List.foldl_cons,List.foldl_cons,ih,commutes]
#print axioms value
end AspisR1.FJn_FoldMap
