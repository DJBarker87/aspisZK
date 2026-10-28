import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_49_1 : poseidonExternalLinear s_49_0 = s_49_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_1
theorem round_49_2 : poseidonFullRound s_49_1 (poseidonExternalInitial 0) = s_49_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_2
theorem round_49_3 : poseidonFullRound s_49_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_49_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_3
theorem round_49_4 : poseidonFullRound s_49_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_49_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_4
theorem round_49_5 : poseidonFullRound s_49_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_49_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_5
theorem round_49_6 : poseidonInternalRound s_49_5 (poseidonInternalConstants 0) = s_49_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_6
theorem round_49_7 : poseidonInternalRound s_49_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_49_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_7
theorem round_49_8 : poseidonInternalRound s_49_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_49_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_8
theorem round_49_9 : poseidonInternalRound s_49_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_49_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_9
theorem round_49_10 : poseidonInternalRound s_49_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_49_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_10
theorem round_49_11 : poseidonInternalRound s_49_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_49_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_11
theorem round_49_12 : poseidonInternalRound s_49_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_49_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_12
theorem round_49_13 : poseidonInternalRound s_49_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_49_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_13
theorem round_49_14 : poseidonInternalRound s_49_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_49_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_14
theorem round_49_15 : poseidonInternalRound s_49_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_49_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_15
theorem round_49_16 : poseidonInternalRound s_49_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_49_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_16
theorem round_49_17 : poseidonInternalRound s_49_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_49_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_17
theorem round_49_18 : poseidonInternalRound s_49_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_49_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_18
theorem round_49_19 : poseidonInternalRound s_49_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_49_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_19
theorem round_49_20 : poseidonFullRound s_49_19 (poseidonExternalFinal 0) = s_49_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_20
theorem round_49_21 : poseidonFullRound s_49_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_49_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_21
theorem round_49_22 : poseidonFullRound s_49_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_49_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_22
theorem round_49_23 : poseidonFullRound s_49_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_49_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_49_23
theorem permutation_49 : poseidonPermutation s_49_0 = s_49_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_49_1,round_49_2,round_49_3,round_49_4,round_49_5,round_49_6,round_49_7,round_49_8,round_49_9,round_49_10,round_49_11,round_49_12,round_49_13,round_49_14,round_49_15,round_49_16,round_49_17,round_49_18,round_49_19,round_49_20,round_49_21,round_49_22,round_49_23]
#print axioms permutation_49
theorem node_49 : nodeCompress (![985515685,670227816,320139735,164221359,586867065,504851391,659699442,1594817757] : Fin 8 → Scalar) ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] = ![210048012,966687588,869731705,823470673,703197799,1759368079,456367603,772376783] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![985515685,670227816,320139735,164221359,586867065,504851391,659699442,1594817757] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_49_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_49]
  funext i
  fin_cases i <;> rfl
#print axioms node_49
end R1Z.PV_RunJoin_OutputModel16
