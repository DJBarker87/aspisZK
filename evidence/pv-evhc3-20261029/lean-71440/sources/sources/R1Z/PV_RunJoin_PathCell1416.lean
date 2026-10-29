import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_14_1 : poseidonExternalLinear s_14_0 = s_14_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_1
theorem round_14_2 : poseidonFullRound s_14_1 (poseidonExternalInitial 0) = s_14_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_2
theorem round_14_3 : poseidonFullRound s_14_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_14_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_3
theorem round_14_4 : poseidonFullRound s_14_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_14_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_4
theorem round_14_5 : poseidonFullRound s_14_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_14_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_5
theorem round_14_6 : poseidonInternalRound s_14_5 (poseidonInternalConstants 0) = s_14_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_6
theorem round_14_7 : poseidonInternalRound s_14_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_14_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_7
theorem round_14_8 : poseidonInternalRound s_14_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_14_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_8
theorem round_14_9 : poseidonInternalRound s_14_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_14_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_9
theorem round_14_10 : poseidonInternalRound s_14_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_14_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_10
theorem round_14_11 : poseidonInternalRound s_14_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_14_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_11
theorem round_14_12 : poseidonInternalRound s_14_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_14_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_12
theorem round_14_13 : poseidonInternalRound s_14_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_14_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_13
theorem round_14_14 : poseidonInternalRound s_14_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_14_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_14
theorem round_14_15 : poseidonInternalRound s_14_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_14_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_15
theorem round_14_16 : poseidonInternalRound s_14_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_14_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_16
theorem round_14_17 : poseidonInternalRound s_14_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_14_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_17
theorem round_14_18 : poseidonInternalRound s_14_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_14_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_18
theorem round_14_19 : poseidonInternalRound s_14_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_14_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_19
theorem round_14_20 : poseidonFullRound s_14_19 (poseidonExternalFinal 0) = s_14_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_20
theorem round_14_21 : poseidonFullRound s_14_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_14_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_21
theorem round_14_22 : poseidonFullRound s_14_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_14_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_22
theorem round_14_23 : poseidonFullRound s_14_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_14_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_23
theorem permutation_14 : poseidonPermutation s_14_0 = s_14_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_14_1,round_14_2,round_14_3,round_14_4,round_14_5,round_14_6,round_14_7,round_14_8,round_14_9,round_14_10,round_14_11,round_14_12,round_14_13,round_14_14,round_14_15,round_14_16,round_14_17,round_14_18,round_14_19,round_14_20,round_14_21,round_14_22,round_14_23]
theorem node_14 : nodeCompress (![1134127212,1758195919,1492236623,1856566444,896074385,533821444,2118230281,1863638021] : Fin 8 → Scalar) ![2141,2158,2175,2192,2209,2226,2243,2260] = ![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1134127212,1758195919,1492236623,1856566444,896074385,533821444,2118230281,1863638021] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2141,2158,2175,2192,2209,2226,2243,2260] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2141,2158,2175,2192,2209,2226,2243,2260] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_14_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_14]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_14
#print axioms node_14
end R1Z.PV_RunJoin_PathModel16
