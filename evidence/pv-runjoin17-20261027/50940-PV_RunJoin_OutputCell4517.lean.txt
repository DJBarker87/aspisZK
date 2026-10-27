import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_45_1 : poseidonExternalLinear s_45_0 = s_45_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_1
theorem round_45_2 : poseidonFullRound s_45_1 (poseidonExternalInitial 0) = s_45_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_2
theorem round_45_3 : poseidonFullRound s_45_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_45_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_3
theorem round_45_4 : poseidonFullRound s_45_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_45_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_4
theorem round_45_5 : poseidonFullRound s_45_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_45_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_5
theorem round_45_6 : poseidonInternalRound s_45_5 (poseidonInternalConstants 0) = s_45_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_6
theorem round_45_7 : poseidonInternalRound s_45_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_45_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_7
theorem round_45_8 : poseidonInternalRound s_45_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_45_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_8
theorem round_45_9 : poseidonInternalRound s_45_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_45_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_9
theorem round_45_10 : poseidonInternalRound s_45_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_45_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_10
theorem round_45_11 : poseidonInternalRound s_45_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_45_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_11
theorem round_45_12 : poseidonInternalRound s_45_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_45_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_12
theorem round_45_13 : poseidonInternalRound s_45_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_45_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_13
theorem round_45_14 : poseidonInternalRound s_45_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_45_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_14
theorem round_45_15 : poseidonInternalRound s_45_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_45_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_15
theorem round_45_16 : poseidonInternalRound s_45_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_45_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_16
theorem round_45_17 : poseidonInternalRound s_45_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_45_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_17
theorem round_45_18 : poseidonInternalRound s_45_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_45_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_18
theorem round_45_19 : poseidonInternalRound s_45_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_45_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_19
theorem round_45_20 : poseidonFullRound s_45_19 (poseidonExternalFinal 0) = s_45_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_20
theorem round_45_21 : poseidonFullRound s_45_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_45_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_21
theorem round_45_22 : poseidonFullRound s_45_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_45_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_22
theorem round_45_23 : poseidonFullRound s_45_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_45_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_45_23
theorem permutation_45 : poseidonPermutation s_45_0 = s_45_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_45_1,round_45_2,round_45_3,round_45_4,round_45_5,round_45_6,round_45_7,round_45_8,round_45_9,round_45_10,round_45_11,round_45_12,round_45_13,round_45_14,round_45_15,round_45_16,round_45_17,round_45_18,round_45_19,round_45_20,round_45_21,round_45_22,round_45_23]
#print axioms permutation_45
theorem node_45 : nodeCompress (![650311058,434968666,41653783,849815005,1944690526,1561873308,545397838,336751789] : Fin 8 → Scalar) ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] = ![1736209514,234715035,487763438,1135092556,1921147183,568436335,1137697966,357096408] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![650311058,434968666,41653783,849815005,1944690526,1561873308,545397838,336751789] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_45_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_45]
  funext i
  fin_cases i <;> rfl
#print axioms node_45
end R1Z.PV_RunJoin_OutputModel16
