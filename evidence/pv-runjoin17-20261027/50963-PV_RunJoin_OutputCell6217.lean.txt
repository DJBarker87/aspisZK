import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_62_1 : poseidonExternalLinear s_62_0 = s_62_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_1
theorem round_62_2 : poseidonFullRound s_62_1 (poseidonExternalInitial 0) = s_62_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_2
theorem round_62_3 : poseidonFullRound s_62_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_62_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_3
theorem round_62_4 : poseidonFullRound s_62_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_62_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_4
theorem round_62_5 : poseidonFullRound s_62_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_62_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_5
theorem round_62_6 : poseidonInternalRound s_62_5 (poseidonInternalConstants 0) = s_62_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_6
theorem round_62_7 : poseidonInternalRound s_62_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_62_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_7
theorem round_62_8 : poseidonInternalRound s_62_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_62_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_8
theorem round_62_9 : poseidonInternalRound s_62_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_62_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_9
theorem round_62_10 : poseidonInternalRound s_62_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_62_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_10
theorem round_62_11 : poseidonInternalRound s_62_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_62_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_11
theorem round_62_12 : poseidonInternalRound s_62_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_62_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_12
theorem round_62_13 : poseidonInternalRound s_62_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_62_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_13
theorem round_62_14 : poseidonInternalRound s_62_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_62_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_14
theorem round_62_15 : poseidonInternalRound s_62_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_62_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_15
theorem round_62_16 : poseidonInternalRound s_62_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_62_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_16
theorem round_62_17 : poseidonInternalRound s_62_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_62_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_17
theorem round_62_18 : poseidonInternalRound s_62_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_62_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_18
theorem round_62_19 : poseidonInternalRound s_62_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_62_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_19
theorem round_62_20 : poseidonFullRound s_62_19 (poseidonExternalFinal 0) = s_62_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_20
theorem round_62_21 : poseidonFullRound s_62_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_62_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_21
theorem round_62_22 : poseidonFullRound s_62_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_62_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_22
theorem round_62_23 : poseidonFullRound s_62_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_62_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_62_23
theorem permutation_62 : poseidonPermutation s_62_0 = s_62_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_62_1,round_62_2,round_62_3,round_62_4,round_62_5,round_62_6,round_62_7,round_62_8,round_62_9,round_62_10,round_62_11,round_62_12,round_62_13,round_62_14,round_62_15,round_62_16,round_62_17,round_62_18,round_62_19,round_62_20,round_62_21,round_62_22,round_62_23]
#print axioms permutation_62
theorem node_62 : nodeCompress (![609870583,958510084,2094278047,743619649,1992887085,2048705761,118223484,1828066596] : Fin 8 → Scalar) ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] = ![1640108137,330515254,212366917,1785570475,1241175939,132178283,1767391975,136033189] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![609870583,958510084,2094278047,743619649,1992887085,2048705761,118223484,1828066596] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_62_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_62]
  funext i
  fin_cases i <;> rfl
#print axioms node_62
end R1Z.PV_RunJoin_OutputModel16
