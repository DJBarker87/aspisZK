import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_41_1 : poseidonExternalLinear s_41_0 = s_41_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_1
theorem round_41_2 : poseidonFullRound s_41_1 (poseidonExternalInitial 0) = s_41_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_2
theorem round_41_3 : poseidonFullRound s_41_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_41_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_3
theorem round_41_4 : poseidonFullRound s_41_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_41_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_4
theorem round_41_5 : poseidonFullRound s_41_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_41_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_5
theorem round_41_6 : poseidonInternalRound s_41_5 (poseidonInternalConstants 0) = s_41_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_6
theorem round_41_7 : poseidonInternalRound s_41_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_41_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_7
theorem round_41_8 : poseidonInternalRound s_41_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_41_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_8
theorem round_41_9 : poseidonInternalRound s_41_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_41_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_9
theorem round_41_10 : poseidonInternalRound s_41_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_41_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_10
theorem round_41_11 : poseidonInternalRound s_41_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_41_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_11
theorem round_41_12 : poseidonInternalRound s_41_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_41_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_12
theorem round_41_13 : poseidonInternalRound s_41_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_41_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_13
theorem round_41_14 : poseidonInternalRound s_41_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_41_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_14
theorem round_41_15 : poseidonInternalRound s_41_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_41_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_15
theorem round_41_16 : poseidonInternalRound s_41_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_41_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_16
theorem round_41_17 : poseidonInternalRound s_41_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_41_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_17
theorem round_41_18 : poseidonInternalRound s_41_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_41_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_18
theorem round_41_19 : poseidonInternalRound s_41_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_41_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_19
theorem round_41_20 : poseidonFullRound s_41_19 (poseidonExternalFinal 0) = s_41_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_20
theorem round_41_21 : poseidonFullRound s_41_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_41_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_21
theorem round_41_22 : poseidonFullRound s_41_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_41_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_22
theorem round_41_23 : poseidonFullRound s_41_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_41_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_41_23
theorem permutation_41 : poseidonPermutation s_41_0 = s_41_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_41_1,round_41_2,round_41_3,round_41_4,round_41_5,round_41_6,round_41_7,round_41_8,round_41_9,round_41_10,round_41_11,round_41_12,round_41_13,round_41_14,round_41_15,round_41_16,round_41_17,round_41_18,round_41_19,round_41_20,round_41_21,round_41_22,round_41_23]
#print axioms permutation_41
theorem node_41 : nodeCompress (![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457] : Fin 8 → Scalar) ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] = ![1939205616,641788683,1281268521,866499727,385183050,1408789791,1189739305,569851020] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_41_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_41]
  funext i
  fin_cases i <;> rfl
#print axioms node_41
end R1Z.PV_RunJoin_OutputModel16
