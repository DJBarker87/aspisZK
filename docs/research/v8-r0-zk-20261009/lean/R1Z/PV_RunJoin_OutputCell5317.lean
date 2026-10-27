import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_53_1 : poseidonExternalLinear s_53_0 = s_53_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_1
theorem round_53_2 : poseidonFullRound s_53_1 (poseidonExternalInitial 0) = s_53_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_2
theorem round_53_3 : poseidonFullRound s_53_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_53_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_3
theorem round_53_4 : poseidonFullRound s_53_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_53_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_4
theorem round_53_5 : poseidonFullRound s_53_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_53_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_5
theorem round_53_6 : poseidonInternalRound s_53_5 (poseidonInternalConstants 0) = s_53_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_6
theorem round_53_7 : poseidonInternalRound s_53_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_53_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_7
theorem round_53_8 : poseidonInternalRound s_53_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_53_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_8
theorem round_53_9 : poseidonInternalRound s_53_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_53_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_9
theorem round_53_10 : poseidonInternalRound s_53_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_53_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_10
theorem round_53_11 : poseidonInternalRound s_53_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_53_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_11
theorem round_53_12 : poseidonInternalRound s_53_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_53_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_12
theorem round_53_13 : poseidonInternalRound s_53_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_53_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_13
theorem round_53_14 : poseidonInternalRound s_53_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_53_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_14
theorem round_53_15 : poseidonInternalRound s_53_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_53_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_15
theorem round_53_16 : poseidonInternalRound s_53_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_53_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_16
theorem round_53_17 : poseidonInternalRound s_53_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_53_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_17
theorem round_53_18 : poseidonInternalRound s_53_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_53_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_18
theorem round_53_19 : poseidonInternalRound s_53_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_53_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_19
theorem round_53_20 : poseidonFullRound s_53_19 (poseidonExternalFinal 0) = s_53_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_20
theorem round_53_21 : poseidonFullRound s_53_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_53_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_21
theorem round_53_22 : poseidonFullRound s_53_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_53_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_22
theorem round_53_23 : poseidonFullRound s_53_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_53_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_53_23
theorem permutation_53 : poseidonPermutation s_53_0 = s_53_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_53_1,round_53_2,round_53_3,round_53_4,round_53_5,round_53_6,round_53_7,round_53_8,round_53_9,round_53_10,round_53_11,round_53_12,round_53_13,round_53_14,round_53_15,round_53_16,round_53_17,round_53_18,round_53_19,round_53_20,round_53_21,round_53_22,round_53_23]
#print axioms permutation_53
theorem node_53 : nodeCompress (![1033316416,1871077402,1557962334,322514877,1982083472,813203847,1866642001,508617919] : Fin 8 → Scalar) ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] = ![1310587138,1547028228,724201667,460418645,1935078033,56710135,329156384,480377036] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1033316416,1871077402,1557962334,322514877,1982083472,813203847,1866642001,508617919] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_53_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_53]
  funext i
  fin_cases i <;> rfl
#print axioms node_53
end R1Z.PV_RunJoin_OutputModel16
