import R0P.Poseidon

set_option autoImplicit false

namespace AspisR1.PoseidonExplicitLowWeightFold

variable {K : Type} [Field K]

def fullLow (low : Fin 16 → K) : K :=
  ([1, 9, 10] : List (Fin 16)).foldl (fun sum row => sum + low row) 0

def internalLow (low : Fin 16 → K) : K :=
  (List.ofFn (fun i : Fin 7 => low ⟨i.val + 2, by omega⟩)).foldl (· + ·) 0

theorem fullLow_explicit (low : Fin 16 → K) :
    fullLow low = ((0 + low 1) + low 9) + low 10 := by
  simp [fullLow, List.foldl_cons]

theorem internalLow_sum (low : Fin 16 → K) :
    internalLow low =
      ∑ i : Fin 7, low ⟨i.val + 2, by omega⟩ := by
  rw [internalLow, R0P.g2_fold_add, zero_add, List.sum_ofFn]

#print axioms fullLow_explicit
#print axioms internalLow_sum

end AspisR1.PoseidonExplicitLowWeightFold
