import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_66_1 : poseidonExternalLinear s_66_0 = s_66_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_1
theorem round_66_2 : poseidonFullRound s_66_1 (poseidonExternalInitial 0) = s_66_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_2
theorem round_66_3 : poseidonFullRound s_66_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_66_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_3
theorem round_66_4 : poseidonFullRound s_66_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_66_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_4
theorem round_66_5 : poseidonFullRound s_66_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_66_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_5
theorem round_66_6 : poseidonInternalRound s_66_5 (poseidonInternalConstants 0) = s_66_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_6
theorem round_66_7 : poseidonInternalRound s_66_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_66_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_7
theorem round_66_8 : poseidonInternalRound s_66_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_66_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_8
theorem round_66_9 : poseidonInternalRound s_66_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_66_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_9
theorem round_66_10 : poseidonInternalRound s_66_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_66_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_10
theorem round_66_11 : poseidonInternalRound s_66_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_66_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_11
theorem round_66_12 : poseidonInternalRound s_66_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_66_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_12
theorem round_66_13 : poseidonInternalRound s_66_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_66_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_13
theorem round_66_14 : poseidonInternalRound s_66_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_66_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_14
theorem round_66_15 : poseidonInternalRound s_66_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_66_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_15
theorem round_66_16 : poseidonInternalRound s_66_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_66_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_16
theorem round_66_17 : poseidonInternalRound s_66_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_66_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_17
theorem round_66_18 : poseidonInternalRound s_66_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_66_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_18
theorem round_66_19 : poseidonInternalRound s_66_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_66_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_19
theorem round_66_20 : poseidonFullRound s_66_19 (poseidonExternalFinal 0) = s_66_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_20
theorem round_66_21 : poseidonFullRound s_66_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_66_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_21
theorem round_66_22 : poseidonFullRound s_66_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_66_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_22
theorem round_66_23 : poseidonFullRound s_66_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_66_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_66_23
theorem permutation_66 : poseidonPermutation s_66_0 = s_66_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_66_1,round_66_2,round_66_3,round_66_4,round_66_5,round_66_6,round_66_7,round_66_8,round_66_9,round_66_10,round_66_11,round_66_12,round_66_13,round_66_14,round_66_15,round_66_16,round_66_17,round_66_18,round_66_19,round_66_20,round_66_21,round_66_22,round_66_23]
#print axioms permutation_66
theorem node_66 : nodeCompress (![779295644,1030234634,105546947,1848021183,1259417564,1402874809,1412830686,1654786357] : Fin 8 → Scalar) ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] = ![641432107,640429421,874903178,930860174,778988106,1148923135,1488375597,266199979] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![779295644,1030234634,105546947,1848021183,1259417564,1402874809,1412830686,1654786357] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_66_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_66]
  funext i
  fin_cases i <;> rfl
#print axioms node_66
end R1Z.PV_RunJoin_OutputModel16
