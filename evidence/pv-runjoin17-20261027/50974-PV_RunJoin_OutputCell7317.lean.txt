import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_73_1 : poseidonExternalLinear s_73_0 = s_73_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_1
theorem round_73_2 : poseidonFullRound s_73_1 (poseidonExternalInitial 0) = s_73_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_2
theorem round_73_3 : poseidonFullRound s_73_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_73_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_3
theorem round_73_4 : poseidonFullRound s_73_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_73_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_4
theorem round_73_5 : poseidonFullRound s_73_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_73_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_5
theorem round_73_6 : poseidonInternalRound s_73_5 (poseidonInternalConstants 0) = s_73_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_6
theorem round_73_7 : poseidonInternalRound s_73_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_73_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_7
theorem round_73_8 : poseidonInternalRound s_73_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_73_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_8
theorem round_73_9 : poseidonInternalRound s_73_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_73_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_9
theorem round_73_10 : poseidonInternalRound s_73_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_73_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_10
theorem round_73_11 : poseidonInternalRound s_73_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_73_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_11
theorem round_73_12 : poseidonInternalRound s_73_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_73_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_12
theorem round_73_13 : poseidonInternalRound s_73_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_73_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_13
theorem round_73_14 : poseidonInternalRound s_73_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_73_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_14
theorem round_73_15 : poseidonInternalRound s_73_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_73_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_15
theorem round_73_16 : poseidonInternalRound s_73_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_73_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_16
theorem round_73_17 : poseidonInternalRound s_73_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_73_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_17
theorem round_73_18 : poseidonInternalRound s_73_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_73_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_18
theorem round_73_19 : poseidonInternalRound s_73_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_73_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_19
theorem round_73_20 : poseidonFullRound s_73_19 (poseidonExternalFinal 0) = s_73_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_20
theorem round_73_21 : poseidonFullRound s_73_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_73_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_21
theorem round_73_22 : poseidonFullRound s_73_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_73_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_22
theorem round_73_23 : poseidonFullRound s_73_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_73_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_73_23
theorem permutation_73 : poseidonPermutation s_73_0 = s_73_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_73_1,round_73_2,round_73_3,round_73_4,round_73_5,round_73_6,round_73_7,round_73_8,round_73_9,round_73_10,round_73_11,round_73_12,round_73_13,round_73_14,round_73_15,round_73_16,round_73_17,round_73_18,round_73_19,round_73_20,round_73_21,round_73_22,round_73_23]
#print axioms permutation_73
theorem node_73 : nodeCompress (![87052585,1514049792,1826519353,387817177,1511331359,351180429,2094192877,1421708941] : Fin 8 → Scalar) ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] = ![1024910236,34897137,119525087,2069845639,34881120,1632903117,1891593814,1830035060] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![87052585,1514049792,1826519353,387817177,1511331359,351180429,2094192877,1421708941] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_73_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_73]
  funext i
  fin_cases i <;> rfl
#print axioms node_73
end R1Z.PV_RunJoin_OutputModel16
