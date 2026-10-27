import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_76_1 : poseidonExternalLinear s_76_0 = s_76_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_1
theorem round_76_2 : poseidonFullRound s_76_1 (poseidonExternalInitial 0) = s_76_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_2
theorem round_76_3 : poseidonFullRound s_76_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_76_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_3
theorem round_76_4 : poseidonFullRound s_76_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_76_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_4
theorem round_76_5 : poseidonFullRound s_76_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_76_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_5
theorem round_76_6 : poseidonInternalRound s_76_5 (poseidonInternalConstants 0) = s_76_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_6
theorem round_76_7 : poseidonInternalRound s_76_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_76_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_7
theorem round_76_8 : poseidonInternalRound s_76_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_76_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_8
theorem round_76_9 : poseidonInternalRound s_76_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_76_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_9
theorem round_76_10 : poseidonInternalRound s_76_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_76_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_10
theorem round_76_11 : poseidonInternalRound s_76_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_76_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_11
theorem round_76_12 : poseidonInternalRound s_76_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_76_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_12
theorem round_76_13 : poseidonInternalRound s_76_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_76_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_13
theorem round_76_14 : poseidonInternalRound s_76_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_76_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_14
theorem round_76_15 : poseidonInternalRound s_76_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_76_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_15
theorem round_76_16 : poseidonInternalRound s_76_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_76_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_16
theorem round_76_17 : poseidonInternalRound s_76_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_76_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_17
theorem round_76_18 : poseidonInternalRound s_76_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_76_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_18
theorem round_76_19 : poseidonInternalRound s_76_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_76_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_19
theorem round_76_20 : poseidonFullRound s_76_19 (poseidonExternalFinal 0) = s_76_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_20
theorem round_76_21 : poseidonFullRound s_76_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_76_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_21
theorem round_76_22 : poseidonFullRound s_76_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_76_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_22
theorem round_76_23 : poseidonFullRound s_76_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_76_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_76_23
theorem permutation_76 : poseidonPermutation s_76_0 = s_76_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_76_1,round_76_2,round_76_3,round_76_4,round_76_5,round_76_6,round_76_7,round_76_8,round_76_9,round_76_10,round_76_11,round_76_12,round_76_13,round_76_14,round_76_15,round_76_16,round_76_17,round_76_18,round_76_19,round_76_20,round_76_21,round_76_22,round_76_23]
#print axioms permutation_76
theorem node_76 : nodeCompress (![1385985564,1312452205,34748210,2022077470,1837706654,827038403,1892640303,370983584] : Fin 8 → Scalar) ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] = ![475693174,322457381,396535705,1030492646,176446941,912396166,1443369366,2063088540] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1385985564,1312452205,34748210,2022077470,1837706654,827038403,1892640303,370983584] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_76_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_76]
  funext i
  fin_cases i <;> rfl
#print axioms node_76
end R1Z.PV_RunJoin_OutputModel16
