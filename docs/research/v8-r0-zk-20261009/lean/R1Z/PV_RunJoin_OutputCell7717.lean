import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_77_1 : poseidonExternalLinear s_77_0 = s_77_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_1
theorem round_77_2 : poseidonFullRound s_77_1 (poseidonExternalInitial 0) = s_77_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_2
theorem round_77_3 : poseidonFullRound s_77_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_77_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_3
theorem round_77_4 : poseidonFullRound s_77_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_77_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_4
theorem round_77_5 : poseidonFullRound s_77_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_77_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_5
theorem round_77_6 : poseidonInternalRound s_77_5 (poseidonInternalConstants 0) = s_77_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_6
theorem round_77_7 : poseidonInternalRound s_77_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_77_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_7
theorem round_77_8 : poseidonInternalRound s_77_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_77_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_8
theorem round_77_9 : poseidonInternalRound s_77_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_77_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_9
theorem round_77_10 : poseidonInternalRound s_77_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_77_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_10
theorem round_77_11 : poseidonInternalRound s_77_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_77_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_11
theorem round_77_12 : poseidonInternalRound s_77_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_77_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_12
theorem round_77_13 : poseidonInternalRound s_77_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_77_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_13
theorem round_77_14 : poseidonInternalRound s_77_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_77_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_14
theorem round_77_15 : poseidonInternalRound s_77_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_77_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_15
theorem round_77_16 : poseidonInternalRound s_77_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_77_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_16
theorem round_77_17 : poseidonInternalRound s_77_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_77_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_17
theorem round_77_18 : poseidonInternalRound s_77_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_77_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_18
theorem round_77_19 : poseidonInternalRound s_77_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_77_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_19
theorem round_77_20 : poseidonFullRound s_77_19 (poseidonExternalFinal 0) = s_77_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_20
theorem round_77_21 : poseidonFullRound s_77_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_77_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_21
theorem round_77_22 : poseidonFullRound s_77_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_77_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_22
theorem round_77_23 : poseidonFullRound s_77_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_77_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_77_23
theorem permutation_77 : poseidonPermutation s_77_0 = s_77_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_77_1,round_77_2,round_77_3,round_77_4,round_77_5,round_77_6,round_77_7,round_77_8,round_77_9,round_77_10,round_77_11,round_77_12,round_77_13,round_77_14,round_77_15,round_77_16,round_77_17,round_77_18,round_77_19,round_77_20,round_77_21,round_77_22,round_77_23]
#print axioms permutation_77
theorem node_77 : nodeCompress (![475693174,322457381,396535705,1030492646,176446941,912396166,1443369366,2063088540] : Fin 8 → Scalar) ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] = ![223002281,116293184,1618212914,1331700281,2109368512,559795428,204366681,229282374] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![475693174,322457381,396535705,1030492646,176446941,912396166,1443369366,2063088540] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_77_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_77]
  funext i
  fin_cases i <;> rfl
#print axioms node_77
end R1Z.PV_RunJoin_OutputModel16
