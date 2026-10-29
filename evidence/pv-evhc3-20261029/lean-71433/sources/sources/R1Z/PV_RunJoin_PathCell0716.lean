import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_7_1 : poseidonExternalLinear s_7_0 = s_7_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_1
theorem round_7_2 : poseidonFullRound s_7_1 (poseidonExternalInitial 0) = s_7_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_2
theorem round_7_3 : poseidonFullRound s_7_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_7_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_3
theorem round_7_4 : poseidonFullRound s_7_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_7_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_4
theorem round_7_5 : poseidonFullRound s_7_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_7_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_5
theorem round_7_6 : poseidonInternalRound s_7_5 (poseidonInternalConstants 0) = s_7_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_6
theorem round_7_7 : poseidonInternalRound s_7_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_7_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_7
theorem round_7_8 : poseidonInternalRound s_7_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_7_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_8
theorem round_7_9 : poseidonInternalRound s_7_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_7_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_9
theorem round_7_10 : poseidonInternalRound s_7_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_7_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_10
theorem round_7_11 : poseidonInternalRound s_7_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_7_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_11
theorem round_7_12 : poseidonInternalRound s_7_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_7_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_12
theorem round_7_13 : poseidonInternalRound s_7_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_7_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_13
theorem round_7_14 : poseidonInternalRound s_7_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_7_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_14
theorem round_7_15 : poseidonInternalRound s_7_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_7_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_15
theorem round_7_16 : poseidonInternalRound s_7_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_7_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_16
theorem round_7_17 : poseidonInternalRound s_7_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_7_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_17
theorem round_7_18 : poseidonInternalRound s_7_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_7_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_18
theorem round_7_19 : poseidonInternalRound s_7_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_7_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_19
theorem round_7_20 : poseidonFullRound s_7_19 (poseidonExternalFinal 0) = s_7_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_20
theorem round_7_21 : poseidonFullRound s_7_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_7_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_21
theorem round_7_22 : poseidonFullRound s_7_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_7_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_22
theorem round_7_23 : poseidonFullRound s_7_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_7_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_7_23
theorem permutation_7 : poseidonPermutation s_7_0 = s_7_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_7_1,round_7_2,round_7_3,round_7_4,round_7_5,round_7_6,round_7_7,round_7_8,round_7_9,round_7_10,round_7_11,round_7_12,round_7_13,round_7_14,round_7_15,round_7_16,round_7_17,round_7_18,round_7_19,round_7_20,round_7_21,round_7_22,round_7_23]
theorem node_7 : nodeCompress (![2001,2018,2035,2052,2069,2086,2103,2120] : Fin 8 → Scalar) ![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] = ![1292573235,1255372443,1043307233,1891352131,920017154,1033317521,170537605,505604950] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2001,2018,2035,2052,2069,2086,2103,2120] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_7_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_7]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_7
#print axioms node_7
end R1Z.PV_RunJoin_PathModel16
