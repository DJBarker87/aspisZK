import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_13_1 : poseidonExternalLinear s_13_0 = s_13_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_1
theorem round_13_2 : poseidonFullRound s_13_1 (poseidonExternalInitial 0) = s_13_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_2
theorem round_13_3 : poseidonFullRound s_13_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_13_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_3
theorem round_13_4 : poseidonFullRound s_13_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_13_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_4
theorem round_13_5 : poseidonFullRound s_13_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_13_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_5
theorem round_13_6 : poseidonInternalRound s_13_5 (poseidonInternalConstants 0) = s_13_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_6
theorem round_13_7 : poseidonInternalRound s_13_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_13_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_7
theorem round_13_8 : poseidonInternalRound s_13_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_13_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_8
theorem round_13_9 : poseidonInternalRound s_13_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_13_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_9
theorem round_13_10 : poseidonInternalRound s_13_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_13_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_10
theorem round_13_11 : poseidonInternalRound s_13_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_13_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_11
theorem round_13_12 : poseidonInternalRound s_13_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_13_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_12
theorem round_13_13 : poseidonInternalRound s_13_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_13_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_13
theorem round_13_14 : poseidonInternalRound s_13_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_13_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_14
theorem round_13_15 : poseidonInternalRound s_13_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_13_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_15
theorem round_13_16 : poseidonInternalRound s_13_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_13_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_16
theorem round_13_17 : poseidonInternalRound s_13_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_13_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_17
theorem round_13_18 : poseidonInternalRound s_13_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_13_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_18
theorem round_13_19 : poseidonInternalRound s_13_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_13_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_19
theorem round_13_20 : poseidonFullRound s_13_19 (poseidonExternalFinal 0) = s_13_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_20
theorem round_13_21 : poseidonFullRound s_13_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_13_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_21
theorem round_13_22 : poseidonFullRound s_13_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_13_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_22
theorem round_13_23 : poseidonFullRound s_13_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_13_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_23
theorem permutation_13 : poseidonPermutation s_13_0 = s_13_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_13_1,round_13_2,round_13_3,round_13_4,round_13_5,round_13_6,round_13_7,round_13_8,round_13_9,round_13_10,round_13_11,round_13_12,round_13_13,round_13_14,round_13_15,round_13_16,round_13_17,round_13_18,round_13_19,round_13_20,round_13_21,round_13_22,round_13_23]
theorem node_13 : nodeCompress (![891777458,519287294,1981395871,1193798350,1897410699,1175699129,1224545956,757035799] : Fin 8 → Scalar) ![2121,2138,2155,2172,2189,2206,2223,2240] = ![1134127212,1758195919,1492236623,1856566444,896074385,533821444,2118230281,1863638021] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![891777458,519287294,1981395871,1193798350,1897410699,1175699129,1224545956,757035799] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2121,2138,2155,2172,2189,2206,2223,2240] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2121,2138,2155,2172,2189,2206,2223,2240] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_13_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_13]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_13
#print axioms node_13
end R1Z.PV_RunJoin_PathModel16
