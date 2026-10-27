import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_56_1 : poseidonExternalLinear s_56_0 = s_56_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_1
theorem round_56_2 : poseidonFullRound s_56_1 (poseidonExternalInitial 0) = s_56_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_2
theorem round_56_3 : poseidonFullRound s_56_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_56_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_3
theorem round_56_4 : poseidonFullRound s_56_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_56_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_4
theorem round_56_5 : poseidonFullRound s_56_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_56_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_5
theorem round_56_6 : poseidonInternalRound s_56_5 (poseidonInternalConstants 0) = s_56_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_6
theorem round_56_7 : poseidonInternalRound s_56_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_56_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_7
theorem round_56_8 : poseidonInternalRound s_56_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_56_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_8
theorem round_56_9 : poseidonInternalRound s_56_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_56_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_9
theorem round_56_10 : poseidonInternalRound s_56_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_56_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_10
theorem round_56_11 : poseidonInternalRound s_56_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_56_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_11
theorem round_56_12 : poseidonInternalRound s_56_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_56_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_12
theorem round_56_13 : poseidonInternalRound s_56_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_56_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_13
theorem round_56_14 : poseidonInternalRound s_56_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_56_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_14
theorem round_56_15 : poseidonInternalRound s_56_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_56_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_15
theorem round_56_16 : poseidonInternalRound s_56_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_56_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_16
theorem round_56_17 : poseidonInternalRound s_56_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_56_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_17
theorem round_56_18 : poseidonInternalRound s_56_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_56_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_18
theorem round_56_19 : poseidonInternalRound s_56_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_56_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_19
theorem round_56_20 : poseidonFullRound s_56_19 (poseidonExternalFinal 0) = s_56_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_20
theorem round_56_21 : poseidonFullRound s_56_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_56_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_21
theorem round_56_22 : poseidonFullRound s_56_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_56_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_22
theorem round_56_23 : poseidonFullRound s_56_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_56_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_56_23
theorem permutation_56 : poseidonPermutation s_56_0 = s_56_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_56_1,round_56_2,round_56_3,round_56_4,round_56_5,round_56_6,round_56_7,round_56_8,round_56_9,round_56_10,round_56_11,round_56_12,round_56_13,round_56_14,round_56_15,round_56_16,round_56_17,round_56_18,round_56_19,round_56_20,round_56_21,round_56_22,round_56_23]
#print axioms permutation_56
theorem node_56 : nodeCompress (![2007593611,263026897,269045574,218491882,465723479,2019127874,1644297524,121114825] : Fin 8 → Scalar) ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] = ![659928130,1737073822,588385416,571209364,294479194,1572976171,358772057,1351134296] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2007593611,263026897,269045574,218491882,465723479,2019127874,1644297524,121114825] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_56_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_56]
  funext i
  fin_cases i <;> rfl
#print axioms node_56
end R1Z.PV_RunJoin_OutputModel16
