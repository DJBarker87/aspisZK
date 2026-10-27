import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_46_1 : poseidonExternalLinear s_46_0 = s_46_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_1
theorem round_46_2 : poseidonFullRound s_46_1 (poseidonExternalInitial 0) = s_46_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_2
theorem round_46_3 : poseidonFullRound s_46_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_46_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_3
theorem round_46_4 : poseidonFullRound s_46_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_46_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_4
theorem round_46_5 : poseidonFullRound s_46_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_46_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_5
theorem round_46_6 : poseidonInternalRound s_46_5 (poseidonInternalConstants 0) = s_46_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_6
theorem round_46_7 : poseidonInternalRound s_46_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_46_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_7
theorem round_46_8 : poseidonInternalRound s_46_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_46_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_8
theorem round_46_9 : poseidonInternalRound s_46_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_46_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_9
theorem round_46_10 : poseidonInternalRound s_46_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_46_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_10
theorem round_46_11 : poseidonInternalRound s_46_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_46_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_11
theorem round_46_12 : poseidonInternalRound s_46_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_46_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_12
theorem round_46_13 : poseidonInternalRound s_46_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_46_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_13
theorem round_46_14 : poseidonInternalRound s_46_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_46_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_14
theorem round_46_15 : poseidonInternalRound s_46_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_46_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_15
theorem round_46_16 : poseidonInternalRound s_46_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_46_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_16
theorem round_46_17 : poseidonInternalRound s_46_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_46_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_17
theorem round_46_18 : poseidonInternalRound s_46_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_46_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_18
theorem round_46_19 : poseidonInternalRound s_46_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_46_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_19
theorem round_46_20 : poseidonFullRound s_46_19 (poseidonExternalFinal 0) = s_46_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_20
theorem round_46_21 : poseidonFullRound s_46_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_46_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_21
theorem round_46_22 : poseidonFullRound s_46_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_46_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_22
theorem round_46_23 : poseidonFullRound s_46_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_46_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_46_23
theorem permutation_46 : poseidonPermutation s_46_0 = s_46_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_46_1,round_46_2,round_46_3,round_46_4,round_46_5,round_46_6,round_46_7,round_46_8,round_46_9,round_46_10,round_46_11,round_46_12,round_46_13,round_46_14,round_46_15,round_46_16,round_46_17,round_46_18,round_46_19,round_46_20,round_46_21,round_46_22,round_46_23]
#print axioms permutation_46
theorem node_46 : nodeCompress (![1736209514,234715035,487763438,1135092556,1921147183,568436335,1137697966,357096408] : Fin 8 → Scalar) ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] = ![874162269,1451641120,2103371390,1001754857,1905791956,1847859879,128353993,1497851806] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1736209514,234715035,487763438,1135092556,1921147183,568436335,1137697966,357096408] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_46_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_46]
  funext i
  fin_cases i <;> rfl
#print axioms node_46
end R1Z.PV_RunJoin_OutputModel16
