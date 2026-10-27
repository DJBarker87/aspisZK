import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_50_1 : poseidonExternalLinear s_50_0 = s_50_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_1
theorem round_50_2 : poseidonFullRound s_50_1 (poseidonExternalInitial 0) = s_50_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_2
theorem round_50_3 : poseidonFullRound s_50_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_50_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_3
theorem round_50_4 : poseidonFullRound s_50_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_50_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_4
theorem round_50_5 : poseidonFullRound s_50_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_50_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_5
theorem round_50_6 : poseidonInternalRound s_50_5 (poseidonInternalConstants 0) = s_50_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_6
theorem round_50_7 : poseidonInternalRound s_50_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_50_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_7
theorem round_50_8 : poseidonInternalRound s_50_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_50_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_8
theorem round_50_9 : poseidonInternalRound s_50_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_50_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_9
theorem round_50_10 : poseidonInternalRound s_50_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_50_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_10
theorem round_50_11 : poseidonInternalRound s_50_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_50_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_11
theorem round_50_12 : poseidonInternalRound s_50_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_50_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_12
theorem round_50_13 : poseidonInternalRound s_50_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_50_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_13
theorem round_50_14 : poseidonInternalRound s_50_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_50_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_14
theorem round_50_15 : poseidonInternalRound s_50_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_50_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_15
theorem round_50_16 : poseidonInternalRound s_50_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_50_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_16
theorem round_50_17 : poseidonInternalRound s_50_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_50_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_17
theorem round_50_18 : poseidonInternalRound s_50_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_50_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_18
theorem round_50_19 : poseidonInternalRound s_50_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_50_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_19
theorem round_50_20 : poseidonFullRound s_50_19 (poseidonExternalFinal 0) = s_50_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_20
theorem round_50_21 : poseidonFullRound s_50_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_50_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_21
theorem round_50_22 : poseidonFullRound s_50_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_50_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_22
theorem round_50_23 : poseidonFullRound s_50_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_50_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_50_23
theorem permutation_50 : poseidonPermutation s_50_0 = s_50_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_50_1,round_50_2,round_50_3,round_50_4,round_50_5,round_50_6,round_50_7,round_50_8,round_50_9,round_50_10,round_50_11,round_50_12,round_50_13,round_50_14,round_50_15,round_50_16,round_50_17,round_50_18,round_50_19,round_50_20,round_50_21,round_50_22,round_50_23]
#print axioms permutation_50
theorem node_50 : nodeCompress (![210048012,966687588,869731705,823470673,703197799,1759368079,456367603,772376783] : Fin 8 → Scalar) ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] = ![1483663627,500119681,2118402728,174107570,654106964,85317403,1579623758,1770549948] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![210048012,966687588,869731705,823470673,703197799,1759368079,456367603,772376783] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_50_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_50]
  funext i
  fin_cases i <;> rfl
#print axioms node_50
end R1Z.PV_RunJoin_OutputModel16
