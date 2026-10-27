import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_72_1 : poseidonExternalLinear s_72_0 = s_72_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_1
theorem round_72_2 : poseidonFullRound s_72_1 (poseidonExternalInitial 0) = s_72_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_2
theorem round_72_3 : poseidonFullRound s_72_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_72_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_3
theorem round_72_4 : poseidonFullRound s_72_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_72_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_4
theorem round_72_5 : poseidonFullRound s_72_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_72_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_5
theorem round_72_6 : poseidonInternalRound s_72_5 (poseidonInternalConstants 0) = s_72_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_6
theorem round_72_7 : poseidonInternalRound s_72_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_72_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_7
theorem round_72_8 : poseidonInternalRound s_72_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_72_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_8
theorem round_72_9 : poseidonInternalRound s_72_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_72_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_9
theorem round_72_10 : poseidonInternalRound s_72_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_72_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_10
theorem round_72_11 : poseidonInternalRound s_72_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_72_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_11
theorem round_72_12 : poseidonInternalRound s_72_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_72_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_12
theorem round_72_13 : poseidonInternalRound s_72_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_72_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_13
theorem round_72_14 : poseidonInternalRound s_72_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_72_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_14
theorem round_72_15 : poseidonInternalRound s_72_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_72_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_15
theorem round_72_16 : poseidonInternalRound s_72_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_72_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_16
theorem round_72_17 : poseidonInternalRound s_72_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_72_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_17
theorem round_72_18 : poseidonInternalRound s_72_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_72_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_18
theorem round_72_19 : poseidonInternalRound s_72_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_72_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_19
theorem round_72_20 : poseidonFullRound s_72_19 (poseidonExternalFinal 0) = s_72_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_20
theorem round_72_21 : poseidonFullRound s_72_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_72_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_21
theorem round_72_22 : poseidonFullRound s_72_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_72_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_22
theorem round_72_23 : poseidonFullRound s_72_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_72_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_72_23
theorem permutation_72 : poseidonPermutation s_72_0 = s_72_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_72_1,round_72_2,round_72_3,round_72_4,round_72_5,round_72_6,round_72_7,round_72_8,round_72_9,round_72_10,round_72_11,round_72_12,round_72_13,round_72_14,round_72_15,round_72_16,round_72_17,round_72_18,round_72_19,round_72_20,round_72_21,round_72_22,round_72_23]
#print axioms permutation_72
theorem node_72 : nodeCompress (![2130322641,1665426257,1206815286,1635654730,225199437,982012671,514446081,115798455] : Fin 8 → Scalar) ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] = ![87052585,1514049792,1826519353,387817177,1511331359,351180429,2094192877,1421708941] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2130322641,1665426257,1206815286,1635654730,225199437,982012671,514446081,115798455] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_72_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_72]
  funext i
  fin_cases i <;> rfl
#print axioms node_72
end R1Z.PV_RunJoin_OutputModel16
