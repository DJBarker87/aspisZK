import FJd_LoopReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_ReferenceDot
open scoped BigOperators
variable {K : Type} [Field K]

theorem fold_value (xs : List (Fin 64)) (a b : Fin 64 → K) (acc : K) :
    xs.foldl (fun v j=>v+a j*b j) acc=acc+(xs.map (fun j=>a j*b j)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih]
    rw [add_assoc]

theorem value (a b : Fin 64 → K) :
    FJd_LoopReference.dot64 a b=∑ i : Fin 64,a i*b i := by
  unfold FJd_LoopReference.dot64
  rw [fold_value,zero_add]
  rw [← List.ofFn_eq_map]
  exact List.sum_ofFn
#print axioms fold_value
#print axioms value
end AspisR1.FJd_ReferenceDot
end
