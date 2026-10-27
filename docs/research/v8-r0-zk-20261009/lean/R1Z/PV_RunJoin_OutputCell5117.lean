import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_51_1 : poseidonExternalLinear s_51_0 = s_51_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_1
theorem round_51_2 : poseidonFullRound s_51_1 (poseidonExternalInitial 0) = s_51_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_2
theorem round_51_3 : poseidonFullRound s_51_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_51_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_3
theorem round_51_4 : poseidonFullRound s_51_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_51_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_4
theorem round_51_5 : poseidonFullRound s_51_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_51_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_5
theorem round_51_6 : poseidonInternalRound s_51_5 (poseidonInternalConstants 0) = s_51_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_6
theorem round_51_7 : poseidonInternalRound s_51_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_51_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_7
theorem round_51_8 : poseidonInternalRound s_51_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_51_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_8
theorem round_51_9 : poseidonInternalRound s_51_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_51_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_9
theorem round_51_10 : poseidonInternalRound s_51_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_51_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_10
theorem round_51_11 : poseidonInternalRound s_51_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_51_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_11
theorem round_51_12 : poseidonInternalRound s_51_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_51_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_12
theorem round_51_13 : poseidonInternalRound s_51_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_51_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_13
theorem round_51_14 : poseidonInternalRound s_51_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_51_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_14
theorem round_51_15 : poseidonInternalRound s_51_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_51_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_15
theorem round_51_16 : poseidonInternalRound s_51_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_51_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_16
theorem round_51_17 : poseidonInternalRound s_51_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_51_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_17
theorem round_51_18 : poseidonInternalRound s_51_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_51_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_18
theorem round_51_19 : poseidonInternalRound s_51_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_51_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_19
theorem round_51_20 : poseidonFullRound s_51_19 (poseidonExternalFinal 0) = s_51_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_20
theorem round_51_21 : poseidonFullRound s_51_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_51_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_21
theorem round_51_22 : poseidonFullRound s_51_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_51_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_22
theorem round_51_23 : poseidonFullRound s_51_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_51_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_51_23
theorem permutation_51 : poseidonPermutation s_51_0 = s_51_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_51_1,round_51_2,round_51_3,round_51_4,round_51_5,round_51_6,round_51_7,round_51_8,round_51_9,round_51_10,round_51_11,round_51_12,round_51_13,round_51_14,round_51_15,round_51_16,round_51_17,round_51_18,round_51_19,round_51_20,round_51_21,round_51_22,round_51_23]
#print axioms permutation_51
theorem node_51 : nodeCompress (![1483663627,500119681,2118402728,174107570,654106964,85317403,1579623758,1770549948] : Fin 8 → Scalar) ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] = ![578338833,1226544375,1719735936,2046596019,1635531819,454303639,1556588950,1520337232] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1483663627,500119681,2118402728,174107570,654106964,85317403,1579623758,1770549948] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_51_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_51]
  funext i
  fin_cases i <;> rfl
#print axioms node_51
end R1Z.PV_RunJoin_OutputModel16
