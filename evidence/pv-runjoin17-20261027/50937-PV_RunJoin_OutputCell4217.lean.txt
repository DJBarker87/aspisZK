import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_42_1 : poseidonExternalLinear s_42_0 = s_42_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_1
theorem round_42_2 : poseidonFullRound s_42_1 (poseidonExternalInitial 0) = s_42_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_2
theorem round_42_3 : poseidonFullRound s_42_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_42_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_3
theorem round_42_4 : poseidonFullRound s_42_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_42_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_4
theorem round_42_5 : poseidonFullRound s_42_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_42_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_5
theorem round_42_6 : poseidonInternalRound s_42_5 (poseidonInternalConstants 0) = s_42_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_6
theorem round_42_7 : poseidonInternalRound s_42_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_42_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_7
theorem round_42_8 : poseidonInternalRound s_42_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_42_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_8
theorem round_42_9 : poseidonInternalRound s_42_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_42_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_9
theorem round_42_10 : poseidonInternalRound s_42_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_42_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_10
theorem round_42_11 : poseidonInternalRound s_42_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_42_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_11
theorem round_42_12 : poseidonInternalRound s_42_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_42_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_12
theorem round_42_13 : poseidonInternalRound s_42_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_42_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_13
theorem round_42_14 : poseidonInternalRound s_42_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_42_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_14
theorem round_42_15 : poseidonInternalRound s_42_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_42_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_15
theorem round_42_16 : poseidonInternalRound s_42_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_42_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_16
theorem round_42_17 : poseidonInternalRound s_42_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_42_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_17
theorem round_42_18 : poseidonInternalRound s_42_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_42_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_18
theorem round_42_19 : poseidonInternalRound s_42_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_42_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_19
theorem round_42_20 : poseidonFullRound s_42_19 (poseidonExternalFinal 0) = s_42_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_20
theorem round_42_21 : poseidonFullRound s_42_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_42_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_21
theorem round_42_22 : poseidonFullRound s_42_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_42_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_22
theorem round_42_23 : poseidonFullRound s_42_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_42_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_42_23
theorem permutation_42 : poseidonPermutation s_42_0 = s_42_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_42_1,round_42_2,round_42_3,round_42_4,round_42_5,round_42_6,round_42_7,round_42_8,round_42_9,round_42_10,round_42_11,round_42_12,round_42_13,round_42_14,round_42_15,round_42_16,round_42_17,round_42_18,round_42_19,round_42_20,round_42_21,round_42_22,round_42_23]
#print axioms permutation_42
theorem node_42 : nodeCompress (![1939205616,641788683,1281268521,866499727,385183050,1408789791,1189739305,569851020] : Fin 8 → Scalar) ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] = ![1133998657,190536997,632216762,2145002820,1218690534,1341831920,1813986794,962659369] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1939205616,641788683,1281268521,866499727,385183050,1408789791,1189739305,569851020] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_42_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_42]
  funext i
  fin_cases i <;> rfl
#print axioms node_42
end R1Z.PV_RunJoin_OutputModel16
