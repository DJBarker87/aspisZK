import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_61_1 : poseidonExternalLinear s_61_0 = s_61_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_1
theorem round_61_2 : poseidonFullRound s_61_1 (poseidonExternalInitial 0) = s_61_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_2
theorem round_61_3 : poseidonFullRound s_61_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_61_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_3
theorem round_61_4 : poseidonFullRound s_61_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_61_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_4
theorem round_61_5 : poseidonFullRound s_61_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_61_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_5
theorem round_61_6 : poseidonInternalRound s_61_5 (poseidonInternalConstants 0) = s_61_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_6
theorem round_61_7 : poseidonInternalRound s_61_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_61_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_7
theorem round_61_8 : poseidonInternalRound s_61_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_61_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_8
theorem round_61_9 : poseidonInternalRound s_61_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_61_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_9
theorem round_61_10 : poseidonInternalRound s_61_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_61_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_10
theorem round_61_11 : poseidonInternalRound s_61_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_61_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_11
theorem round_61_12 : poseidonInternalRound s_61_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_61_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_12
theorem round_61_13 : poseidonInternalRound s_61_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_61_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_13
theorem round_61_14 : poseidonInternalRound s_61_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_61_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_14
theorem round_61_15 : poseidonInternalRound s_61_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_61_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_15
theorem round_61_16 : poseidonInternalRound s_61_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_61_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_16
theorem round_61_17 : poseidonInternalRound s_61_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_61_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_17
theorem round_61_18 : poseidonInternalRound s_61_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_61_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_18
theorem round_61_19 : poseidonInternalRound s_61_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_61_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_19
theorem round_61_20 : poseidonFullRound s_61_19 (poseidonExternalFinal 0) = s_61_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_20
theorem round_61_21 : poseidonFullRound s_61_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_61_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_21
theorem round_61_22 : poseidonFullRound s_61_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_61_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_22
theorem round_61_23 : poseidonFullRound s_61_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_61_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_61_23
theorem permutation_61 : poseidonPermutation s_61_0 = s_61_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_61_1,round_61_2,round_61_3,round_61_4,round_61_5,round_61_6,round_61_7,round_61_8,round_61_9,round_61_10,round_61_11,round_61_12,round_61_13,round_61_14,round_61_15,round_61_16,round_61_17,round_61_18,round_61_19,round_61_20,round_61_21,round_61_22,round_61_23]
#print axioms permutation_61
theorem node_61 : nodeCompress (![1635444076,565453809,2007649881,905247732,1187015924,827186728,137720039,588419202] : Fin 8 → Scalar) ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] = ![609870583,958510084,2094278047,743619649,1992887085,2048705761,118223484,1828066596] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1635444076,565453809,2007649881,905247732,1187015924,827186728,137720039,588419202] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_61_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_61]
  funext i
  fin_cases i <;> rfl
#print axioms node_61
end R1Z.PV_RunJoin_OutputModel16
