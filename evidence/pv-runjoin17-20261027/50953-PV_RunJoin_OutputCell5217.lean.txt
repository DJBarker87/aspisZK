import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_52_1 : poseidonExternalLinear s_52_0 = s_52_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_1
theorem round_52_2 : poseidonFullRound s_52_1 (poseidonExternalInitial 0) = s_52_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_2
theorem round_52_3 : poseidonFullRound s_52_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_52_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_3
theorem round_52_4 : poseidonFullRound s_52_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_52_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_4
theorem round_52_5 : poseidonFullRound s_52_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_52_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_5
theorem round_52_6 : poseidonInternalRound s_52_5 (poseidonInternalConstants 0) = s_52_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_6
theorem round_52_7 : poseidonInternalRound s_52_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_52_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_7
theorem round_52_8 : poseidonInternalRound s_52_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_52_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_8
theorem round_52_9 : poseidonInternalRound s_52_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_52_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_9
theorem round_52_10 : poseidonInternalRound s_52_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_52_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_10
theorem round_52_11 : poseidonInternalRound s_52_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_52_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_11
theorem round_52_12 : poseidonInternalRound s_52_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_52_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_12
theorem round_52_13 : poseidonInternalRound s_52_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_52_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_13
theorem round_52_14 : poseidonInternalRound s_52_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_52_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_14
theorem round_52_15 : poseidonInternalRound s_52_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_52_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_15
theorem round_52_16 : poseidonInternalRound s_52_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_52_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_16
theorem round_52_17 : poseidonInternalRound s_52_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_52_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_17
theorem round_52_18 : poseidonInternalRound s_52_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_52_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_18
theorem round_52_19 : poseidonInternalRound s_52_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_52_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_19
theorem round_52_20 : poseidonFullRound s_52_19 (poseidonExternalFinal 0) = s_52_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_20
theorem round_52_21 : poseidonFullRound s_52_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_52_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_21
theorem round_52_22 : poseidonFullRound s_52_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_52_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_22
theorem round_52_23 : poseidonFullRound s_52_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_52_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_52_23
theorem permutation_52 : poseidonPermutation s_52_0 = s_52_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_52_1,round_52_2,round_52_3,round_52_4,round_52_5,round_52_6,round_52_7,round_52_8,round_52_9,round_52_10,round_52_11,round_52_12,round_52_13,round_52_14,round_52_15,round_52_16,round_52_17,round_52_18,round_52_19,round_52_20,round_52_21,round_52_22,round_52_23]
#print axioms permutation_52
theorem node_52 : nodeCompress (![578338833,1226544375,1719735936,2046596019,1635531819,454303639,1556588950,1520337232] : Fin 8 → Scalar) ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] = ![1033316416,1871077402,1557962334,322514877,1982083472,813203847,1866642001,508617919] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![578338833,1226544375,1719735936,2046596019,1635531819,454303639,1556588950,1520337232] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_52_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_52]
  funext i
  fin_cases i <;> rfl
#print axioms node_52
end R1Z.PV_RunJoin_OutputModel16
