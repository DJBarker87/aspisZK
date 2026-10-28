import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_15_1 : poseidonExternalLinear s_15_0 = s_15_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_1
theorem round_15_2 : poseidonFullRound s_15_1 (poseidonExternalInitial 0) = s_15_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_2
theorem round_15_3 : poseidonFullRound s_15_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_15_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_3
theorem round_15_4 : poseidonFullRound s_15_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_15_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_4
theorem round_15_5 : poseidonFullRound s_15_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_15_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_5
theorem round_15_6 : poseidonInternalRound s_15_5 (poseidonInternalConstants 0) = s_15_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_6
theorem round_15_7 : poseidonInternalRound s_15_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_15_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_7
theorem round_15_8 : poseidonInternalRound s_15_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_15_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_8
theorem round_15_9 : poseidonInternalRound s_15_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_15_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_9
theorem round_15_10 : poseidonInternalRound s_15_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_15_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_10
theorem round_15_11 : poseidonInternalRound s_15_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_15_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_11
theorem round_15_12 : poseidonInternalRound s_15_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_15_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_12
theorem round_15_13 : poseidonInternalRound s_15_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_15_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_13
theorem round_15_14 : poseidonInternalRound s_15_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_15_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_14
theorem round_15_15 : poseidonInternalRound s_15_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_15_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_15
theorem round_15_16 : poseidonInternalRound s_15_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_15_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_16
theorem round_15_17 : poseidonInternalRound s_15_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_15_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_17
theorem round_15_18 : poseidonInternalRound s_15_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_15_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_18
theorem round_15_19 : poseidonInternalRound s_15_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_15_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_19
theorem round_15_20 : poseidonFullRound s_15_19 (poseidonExternalFinal 0) = s_15_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_20
theorem round_15_21 : poseidonFullRound s_15_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_15_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_21
theorem round_15_22 : poseidonFullRound s_15_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_15_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_22
theorem round_15_23 : poseidonFullRound s_15_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_15_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_23
theorem permutation_15 : poseidonPermutation s_15_0 = s_15_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_15_1,round_15_2,round_15_3,round_15_4,round_15_5,round_15_6,round_15_7,round_15_8,round_15_9,round_15_10,round_15_11,round_15_12,round_15_13,round_15_14,round_15_15,round_15_16,round_15_17,round_15_18,round_15_19,round_15_20,round_15_21,round_15_22,round_15_23]
theorem node_15 : nodeCompress (![2161,2178,2195,2212,2229,2246,2263,2280] : Fin 8 → Scalar) ![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080] = ![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2161,2178,2195,2212,2229,2246,2263,2280] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_15_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_15]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_15
#print axioms node_15
end R1Z.PV_RunJoin_PathModel16
