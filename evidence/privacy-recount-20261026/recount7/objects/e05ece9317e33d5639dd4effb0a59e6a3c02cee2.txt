import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_57_1 : poseidonExternalLinear s_57_0 = s_57_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_1
theorem round_57_2 : poseidonFullRound s_57_1 (poseidonExternalInitial 0) = s_57_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_2
theorem round_57_3 : poseidonFullRound s_57_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_57_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_3
theorem round_57_4 : poseidonFullRound s_57_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_57_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_4
theorem round_57_5 : poseidonFullRound s_57_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_57_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_5
theorem round_57_6 : poseidonInternalRound s_57_5 (poseidonInternalConstants 0) = s_57_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_6
theorem round_57_7 : poseidonInternalRound s_57_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_57_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_7
theorem round_57_8 : poseidonInternalRound s_57_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_57_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_8
theorem round_57_9 : poseidonInternalRound s_57_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_57_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_9
theorem round_57_10 : poseidonInternalRound s_57_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_57_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_10
theorem round_57_11 : poseidonInternalRound s_57_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_57_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_11
theorem round_57_12 : poseidonInternalRound s_57_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_57_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_12
theorem round_57_13 : poseidonInternalRound s_57_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_57_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_13
theorem round_57_14 : poseidonInternalRound s_57_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_57_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_14
theorem round_57_15 : poseidonInternalRound s_57_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_57_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_15
theorem round_57_16 : poseidonInternalRound s_57_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_57_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_16
theorem round_57_17 : poseidonInternalRound s_57_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_57_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_17
theorem round_57_18 : poseidonInternalRound s_57_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_57_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_18
theorem round_57_19 : poseidonInternalRound s_57_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_57_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_19
theorem round_57_20 : poseidonFullRound s_57_19 (poseidonExternalFinal 0) = s_57_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_20
theorem round_57_21 : poseidonFullRound s_57_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_57_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_21
theorem round_57_22 : poseidonFullRound s_57_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_57_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_22
theorem round_57_23 : poseidonFullRound s_57_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_57_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_57_23
theorem permutation_57 : poseidonPermutation s_57_0 = s_57_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_57_1,round_57_2,round_57_3,round_57_4,round_57_5,round_57_6,round_57_7,round_57_8,round_57_9,round_57_10,round_57_11,round_57_12,round_57_13,round_57_14,round_57_15,round_57_16,round_57_17,round_57_18,round_57_19,round_57_20,round_57_21,round_57_22,round_57_23]
#print axioms permutation_57
theorem node_57 : nodeCompress (![659928130,1737073822,588385416,571209364,294479194,1572976171,358772057,1351134296] : Fin 8 → Scalar) ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] = ![295651292,1528951695,967845926,1002855730,1691775382,1825776613,369526834,1655898863] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![659928130,1737073822,588385416,571209364,294479194,1572976171,358772057,1351134296] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_57_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_57]
  funext i
  fin_cases i <;> rfl
#print axioms node_57
end R1Z.PV_RunJoin_OutputModel16
