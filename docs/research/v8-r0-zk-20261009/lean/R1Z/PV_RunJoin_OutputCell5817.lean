import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_58_1 : poseidonExternalLinear s_58_0 = s_58_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_1
theorem round_58_2 : poseidonFullRound s_58_1 (poseidonExternalInitial 0) = s_58_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_2
theorem round_58_3 : poseidonFullRound s_58_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_58_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_3
theorem round_58_4 : poseidonFullRound s_58_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_58_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_4
theorem round_58_5 : poseidonFullRound s_58_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_58_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_5
theorem round_58_6 : poseidonInternalRound s_58_5 (poseidonInternalConstants 0) = s_58_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_6
theorem round_58_7 : poseidonInternalRound s_58_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_58_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_7
theorem round_58_8 : poseidonInternalRound s_58_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_58_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_8
theorem round_58_9 : poseidonInternalRound s_58_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_58_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_9
theorem round_58_10 : poseidonInternalRound s_58_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_58_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_10
theorem round_58_11 : poseidonInternalRound s_58_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_58_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_11
theorem round_58_12 : poseidonInternalRound s_58_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_58_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_12
theorem round_58_13 : poseidonInternalRound s_58_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_58_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_13
theorem round_58_14 : poseidonInternalRound s_58_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_58_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_14
theorem round_58_15 : poseidonInternalRound s_58_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_58_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_15
theorem round_58_16 : poseidonInternalRound s_58_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_58_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_16
theorem round_58_17 : poseidonInternalRound s_58_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_58_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_17
theorem round_58_18 : poseidonInternalRound s_58_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_58_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_18
theorem round_58_19 : poseidonInternalRound s_58_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_58_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_19
theorem round_58_20 : poseidonFullRound s_58_19 (poseidonExternalFinal 0) = s_58_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_20
theorem round_58_21 : poseidonFullRound s_58_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_58_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_21
theorem round_58_22 : poseidonFullRound s_58_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_58_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_22
theorem round_58_23 : poseidonFullRound s_58_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_58_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_58_23
theorem permutation_58 : poseidonPermutation s_58_0 = s_58_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_58_1,round_58_2,round_58_3,round_58_4,round_58_5,round_58_6,round_58_7,round_58_8,round_58_9,round_58_10,round_58_11,round_58_12,round_58_13,round_58_14,round_58_15,round_58_16,round_58_17,round_58_18,round_58_19,round_58_20,round_58_21,round_58_22,round_58_23]
#print axioms permutation_58
theorem node_58 : nodeCompress (![295651292,1528951695,967845926,1002855730,1691775382,1825776613,369526834,1655898863] : Fin 8 → Scalar) ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] = ![1660714618,58624303,617770228,599383446,771361068,1834589194,51322319,276611708] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![295651292,1528951695,967845926,1002855730,1691775382,1825776613,369526834,1655898863] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_58_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_58]
  funext i
  fin_cases i <;> rfl
#print axioms node_58
end R1Z.PV_RunJoin_OutputModel16
