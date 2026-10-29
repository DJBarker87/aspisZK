import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_18_1 : poseidonExternalLinear s_18_0 = s_18_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_1
theorem round_18_2 : poseidonFullRound s_18_1 (poseidonExternalInitial 0) = s_18_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_2
theorem round_18_3 : poseidonFullRound s_18_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_18_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_3
theorem round_18_4 : poseidonFullRound s_18_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_18_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_4
theorem round_18_5 : poseidonFullRound s_18_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_18_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_5
theorem round_18_6 : poseidonInternalRound s_18_5 (poseidonInternalConstants 0) = s_18_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_6
theorem round_18_7 : poseidonInternalRound s_18_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_18_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_7
theorem round_18_8 : poseidonInternalRound s_18_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_18_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_8
theorem round_18_9 : poseidonInternalRound s_18_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_18_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_9
theorem round_18_10 : poseidonInternalRound s_18_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_18_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_10
theorem round_18_11 : poseidonInternalRound s_18_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_18_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_11
theorem round_18_12 : poseidonInternalRound s_18_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_18_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_12
theorem round_18_13 : poseidonInternalRound s_18_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_18_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_13
theorem round_18_14 : poseidonInternalRound s_18_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_18_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_14
theorem round_18_15 : poseidonInternalRound s_18_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_18_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_15
theorem round_18_16 : poseidonInternalRound s_18_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_18_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_16
theorem round_18_17 : poseidonInternalRound s_18_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_18_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_17
theorem round_18_18 : poseidonInternalRound s_18_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_18_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_18
theorem round_18_19 : poseidonInternalRound s_18_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_18_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_19
theorem round_18_20 : poseidonFullRound s_18_19 (poseidonExternalFinal 0) = s_18_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_20
theorem round_18_21 : poseidonFullRound s_18_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_18_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_21
theorem round_18_22 : poseidonFullRound s_18_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_18_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_22
theorem round_18_23 : poseidonFullRound s_18_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_18_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_18_23
theorem permutation_18 : poseidonPermutation s_18_0 = s_18_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_18_1,round_18_2,round_18_3,round_18_4,round_18_5,round_18_6,round_18_7,round_18_8,round_18_9,round_18_10,round_18_11,round_18_12,round_18_13,round_18_14,round_18_15,round_18_16,round_18_17,round_18_18,round_18_19,round_18_20,round_18_21,round_18_22,round_18_23]
theorem node_18 : nodeCompress (![1843107484,377090426,1232835735,1598963180,1994057985,1261374148,1230772006,1621463387] : Fin 8 → Scalar) ![2221,2238,2255,2272,2289,2306,2323,2340] = ![784754526,653487580,1331396859,1248357024,70404971,1215624494,880337038,1016952666] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1843107484,377090426,1232835735,1598963180,1994057985,1261374148,1230772006,1621463387] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2221,2238,2255,2272,2289,2306,2323,2340] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2221,2238,2255,2272,2289,2306,2323,2340] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_18_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_18]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_18
#print axioms node_18
end R1Z.PV_RunJoin_PathModel16
