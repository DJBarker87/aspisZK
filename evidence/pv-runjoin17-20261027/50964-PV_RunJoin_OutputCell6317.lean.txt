import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_63_1 : poseidonExternalLinear s_63_0 = s_63_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_1
theorem round_63_2 : poseidonFullRound s_63_1 (poseidonExternalInitial 0) = s_63_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_2
theorem round_63_3 : poseidonFullRound s_63_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_63_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_3
theorem round_63_4 : poseidonFullRound s_63_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_63_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_4
theorem round_63_5 : poseidonFullRound s_63_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_63_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_5
theorem round_63_6 : poseidonInternalRound s_63_5 (poseidonInternalConstants 0) = s_63_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_6
theorem round_63_7 : poseidonInternalRound s_63_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_63_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_7
theorem round_63_8 : poseidonInternalRound s_63_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_63_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_8
theorem round_63_9 : poseidonInternalRound s_63_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_63_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_9
theorem round_63_10 : poseidonInternalRound s_63_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_63_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_10
theorem round_63_11 : poseidonInternalRound s_63_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_63_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_11
theorem round_63_12 : poseidonInternalRound s_63_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_63_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_12
theorem round_63_13 : poseidonInternalRound s_63_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_63_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_13
theorem round_63_14 : poseidonInternalRound s_63_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_63_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_14
theorem round_63_15 : poseidonInternalRound s_63_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_63_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_15
theorem round_63_16 : poseidonInternalRound s_63_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_63_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_16
theorem round_63_17 : poseidonInternalRound s_63_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_63_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_17
theorem round_63_18 : poseidonInternalRound s_63_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_63_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_18
theorem round_63_19 : poseidonInternalRound s_63_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_63_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_19
theorem round_63_20 : poseidonFullRound s_63_19 (poseidonExternalFinal 0) = s_63_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_20
theorem round_63_21 : poseidonFullRound s_63_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_63_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_21
theorem round_63_22 : poseidonFullRound s_63_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_63_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_22
theorem round_63_23 : poseidonFullRound s_63_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_63_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_63_23
theorem permutation_63 : poseidonPermutation s_63_0 = s_63_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_63_1,round_63_2,round_63_3,round_63_4,round_63_5,round_63_6,round_63_7,round_63_8,round_63_9,round_63_10,round_63_11,round_63_12,round_63_13,round_63_14,round_63_15,round_63_16,round_63_17,round_63_18,round_63_19,round_63_20,round_63_21,round_63_22,round_63_23]
#print axioms permutation_63
theorem node_63 : nodeCompress (![1640108137,330515254,212366917,1785570475,1241175939,132178283,1767391975,136033189] : Fin 8 → Scalar) ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] = ![432585881,1344347431,436199667,1321219941,1344313237,719981873,669780265,1723074008] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1640108137,330515254,212366917,1785570475,1241175939,132178283,1767391975,136033189] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_63_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_63]
  funext i
  fin_cases i <;> rfl
#print axioms node_63
end R1Z.PV_RunJoin_OutputModel16
