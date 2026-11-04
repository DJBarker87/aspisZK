import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_17_1 : poseidonExternalLinear s_17_0 = s_17_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_1
theorem round_17_2 : poseidonFullRound s_17_1 (poseidonExternalInitial 0) = s_17_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_2
theorem round_17_3 : poseidonFullRound s_17_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_17_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_3
theorem round_17_4 : poseidonFullRound s_17_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_17_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_4
theorem round_17_5 : poseidonFullRound s_17_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_17_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_5
theorem round_17_6 : poseidonInternalRound s_17_5 (poseidonInternalConstants 0) = s_17_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_6
theorem round_17_7 : poseidonInternalRound s_17_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_17_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_7
theorem round_17_8 : poseidonInternalRound s_17_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_17_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_8
theorem round_17_9 : poseidonInternalRound s_17_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_17_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_9
theorem round_17_10 : poseidonInternalRound s_17_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_17_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_10
theorem round_17_11 : poseidonInternalRound s_17_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_17_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_11
theorem round_17_12 : poseidonInternalRound s_17_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_17_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_12
theorem round_17_13 : poseidonInternalRound s_17_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_17_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_13
theorem round_17_14 : poseidonInternalRound s_17_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_17_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_14
theorem round_17_15 : poseidonInternalRound s_17_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_17_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_15
theorem round_17_16 : poseidonInternalRound s_17_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_17_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_16
theorem round_17_17 : poseidonInternalRound s_17_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_17_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_17
theorem round_17_18 : poseidonInternalRound s_17_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_17_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_18
theorem round_17_19 : poseidonInternalRound s_17_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_17_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_19
theorem round_17_20 : poseidonFullRound s_17_19 (poseidonExternalFinal 0) = s_17_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_20
theorem round_17_21 : poseidonFullRound s_17_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_17_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_21
theorem round_17_22 : poseidonFullRound s_17_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_17_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_22
theorem round_17_23 : poseidonFullRound s_17_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_17_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_23
theorem permutation_17 : poseidonPermutation s_17_0 = s_17_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_17_1,round_17_2,round_17_3,round_17_4,round_17_5,round_17_6,round_17_7,round_17_8,round_17_9,round_17_10,round_17_11,round_17_12,round_17_13,round_17_14,round_17_15,round_17_16,round_17_17,round_17_18,round_17_19,round_17_20,round_17_21,round_17_22,round_17_23]
theorem node_17 : nodeCompress (![620824211,300099494,1668011682,374649414,1359169338,1742041081,1575185854,1782871725] : Fin 8 → Scalar) ![2201,2218,2235,2252,2269,2286,2303,2320] = ![1843107484,377090426,1232835735,1598963180,1994057985,1261374148,1230772006,1621463387] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![620824211,300099494,1668011682,374649414,1359169338,1742041081,1575185854,1782871725] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2201,2218,2235,2252,2269,2286,2303,2320] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2201,2218,2235,2252,2269,2286,2303,2320] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_17_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_17]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_17
#print axioms node_17
end R1Z.PV_RunJoin_PathModel16
