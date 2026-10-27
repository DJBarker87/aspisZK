import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_60_1 : poseidonExternalLinear s_60_0 = s_60_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_1
theorem round_60_2 : poseidonFullRound s_60_1 (poseidonExternalInitial 0) = s_60_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_2
theorem round_60_3 : poseidonFullRound s_60_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_60_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_3
theorem round_60_4 : poseidonFullRound s_60_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_60_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_4
theorem round_60_5 : poseidonFullRound s_60_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_60_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_5
theorem round_60_6 : poseidonInternalRound s_60_5 (poseidonInternalConstants 0) = s_60_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_6
theorem round_60_7 : poseidonInternalRound s_60_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_60_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_7
theorem round_60_8 : poseidonInternalRound s_60_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_60_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_8
theorem round_60_9 : poseidonInternalRound s_60_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_60_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_9
theorem round_60_10 : poseidonInternalRound s_60_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_60_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_10
theorem round_60_11 : poseidonInternalRound s_60_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_60_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_11
theorem round_60_12 : poseidonInternalRound s_60_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_60_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_12
theorem round_60_13 : poseidonInternalRound s_60_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_60_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_13
theorem round_60_14 : poseidonInternalRound s_60_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_60_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_14
theorem round_60_15 : poseidonInternalRound s_60_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_60_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_15
theorem round_60_16 : poseidonInternalRound s_60_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_60_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_16
theorem round_60_17 : poseidonInternalRound s_60_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_60_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_17
theorem round_60_18 : poseidonInternalRound s_60_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_60_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_18
theorem round_60_19 : poseidonInternalRound s_60_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_60_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_19
theorem round_60_20 : poseidonFullRound s_60_19 (poseidonExternalFinal 0) = s_60_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_20
theorem round_60_21 : poseidonFullRound s_60_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_60_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_21
theorem round_60_22 : poseidonFullRound s_60_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_60_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_22
theorem round_60_23 : poseidonFullRound s_60_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_60_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_60_23
theorem permutation_60 : poseidonPermutation s_60_0 = s_60_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_60_1,round_60_2,round_60_3,round_60_4,round_60_5,round_60_6,round_60_7,round_60_8,round_60_9,round_60_10,round_60_11,round_60_12,round_60_13,round_60_14,round_60_15,round_60_16,round_60_17,round_60_18,round_60_19,round_60_20,round_60_21,round_60_22,round_60_23]
#print axioms permutation_60
theorem node_60 : nodeCompress (![1186265903,415151008,1902434632,1450931092,922955725,1977809658,160284130,1987330095] : Fin 8 → Scalar) ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] = ![1915027034,1282510897,1183742216,189326495,737878707,1491662218,555560417,611527247] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1186265903,415151008,1902434632,1450931092,922955725,1977809658,160284130,1987330095] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_60_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_60]
  funext i
  fin_cases i <;> rfl
#print axioms node_60
end R1Z.PV_RunJoin_OutputModel16
