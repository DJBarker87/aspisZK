import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_16_1 : poseidonExternalLinear s_16_0 = s_16_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_1
theorem round_16_2 : poseidonFullRound s_16_1 (poseidonExternalInitial 0) = s_16_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_2
theorem round_16_3 : poseidonFullRound s_16_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_16_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_3
theorem round_16_4 : poseidonFullRound s_16_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_16_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_4
theorem round_16_5 : poseidonFullRound s_16_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_16_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_5
theorem round_16_6 : poseidonInternalRound s_16_5 (poseidonInternalConstants 0) = s_16_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_6
theorem round_16_7 : poseidonInternalRound s_16_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_16_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_7
theorem round_16_8 : poseidonInternalRound s_16_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_16_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_8
theorem round_16_9 : poseidonInternalRound s_16_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_16_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_9
theorem round_16_10 : poseidonInternalRound s_16_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_16_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_10
theorem round_16_11 : poseidonInternalRound s_16_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_16_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_11
theorem round_16_12 : poseidonInternalRound s_16_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_16_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_12
theorem round_16_13 : poseidonInternalRound s_16_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_16_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_13
theorem round_16_14 : poseidonInternalRound s_16_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_16_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_14
theorem round_16_15 : poseidonInternalRound s_16_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_16_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_15
theorem round_16_16 : poseidonInternalRound s_16_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_16_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_16
theorem round_16_17 : poseidonInternalRound s_16_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_16_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_17
theorem round_16_18 : poseidonInternalRound s_16_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_16_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_18
theorem round_16_19 : poseidonInternalRound s_16_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_16_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_19
theorem round_16_20 : poseidonFullRound s_16_19 (poseidonExternalFinal 0) = s_16_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_20
theorem round_16_21 : poseidonFullRound s_16_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_16_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_21
theorem round_16_22 : poseidonFullRound s_16_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_16_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_22
theorem round_16_23 : poseidonFullRound s_16_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_16_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_23
theorem permutation_16 : poseidonPermutation s_16_0 = s_16_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_16_1,round_16_2,round_16_3,round_16_4,round_16_5,round_16_6,round_16_7,round_16_8,round_16_9,round_16_10,round_16_11,round_16_12,round_16_13,round_16_14,round_16_15,round_16_16,round_16_17,round_16_18,round_16_19,round_16_20,round_16_21,round_16_22,round_16_23]
theorem node_16 : nodeCompress (![2181,2198,2215,2232,2249,2266,2283,2300] : Fin 8 → Scalar) ![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662] = ![620824211,300099494,1668011682,374649414,1359169338,1742041081,1575185854,1782871725] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2181,2198,2215,2232,2249,2266,2283,2300] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_16_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_16]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_16
#print axioms node_16
end R1Z.PV_RunJoin_PathModel16
