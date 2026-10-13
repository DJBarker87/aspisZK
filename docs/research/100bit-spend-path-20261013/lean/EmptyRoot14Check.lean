import R1EmptyRoot14Data
import R1PoseidonChain
import R1AppendNode

/-! A literal empty-root row checked as a chain of independent one-round transitions. -/
/-! The generator keeps each transition as a small `decide`; it emits no full-chain `decide`. -/
set_option autoImplicit false
namespace AspisR1.EmptyRoot14Check
open R0P AspisCircleGroupOrder AspisR1.EmptyRoot14Data

def trajectory : Fin 24 → (Fin 16 → ZMod P) :=
  ![s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23]

theorem leading : s1 = poseidonExternalLinear s0 := by decide

theorem initial_0 : s2 = poseidonFullRound s1 (poseidonExternalInitial 0) := by decide

theorem initial_1 : s3 = poseidonFullRound s2 (poseidonExternalInitial 1) := by decide

theorem initial_2 : s4 = poseidonFullRound s3 (poseidonExternalInitial 2) := by decide

theorem initial_3 : s5 = poseidonFullRound s4 (poseidonExternalInitial 3) := by decide

theorem internal_0 : s6 = poseidonInternalRound s5 (poseidonInternalConstants 0) := by decide

theorem internal_1 : s7 = poseidonInternalRound s6 (poseidonInternalConstants 1) := by decide

theorem internal_2 : s8 = poseidonInternalRound s7 (poseidonInternalConstants 2) := by decide

theorem internal_3 : s9 = poseidonInternalRound s8 (poseidonInternalConstants 3) := by decide

theorem internal_4 : s10 = poseidonInternalRound s9 (poseidonInternalConstants 4) := by decide

theorem internal_5 : s11 = poseidonInternalRound s10 (poseidonInternalConstants 5) := by decide

theorem internal_6 : s12 = poseidonInternalRound s11 (poseidonInternalConstants 6) := by decide

theorem internal_7 : s13 = poseidonInternalRound s12 (poseidonInternalConstants 7) := by decide

theorem internal_8 : s14 = poseidonInternalRound s13 (poseidonInternalConstants 8) := by decide

theorem internal_9 : s15 = poseidonInternalRound s14 (poseidonInternalConstants 9) := by decide

theorem internal_10 : s16 = poseidonInternalRound s15 (poseidonInternalConstants 10) := by decide

theorem internal_11 : s17 = poseidonInternalRound s16 (poseidonInternalConstants 11) := by decide

theorem internal_12 : s18 = poseidonInternalRound s17 (poseidonInternalConstants 12) := by decide

theorem internal_13 : s19 = poseidonInternalRound s18 (poseidonInternalConstants 13) := by decide

theorem final_0 : s20 = poseidonFullRound s19 (poseidonExternalFinal 0) := by decide

theorem final_1 : s21 = poseidonFullRound s20 (poseidonExternalFinal 1) := by decide

theorem final_2 : s22 = poseidonFullRound s21 (poseidonExternalFinal 2) := by decide

theorem final_3 : s23 = poseidonFullRound s22 (poseidonExternalFinal 3) := by decide

theorem permutation : poseidonPermutation s0 = s23 := by
  apply poseidon_chain trajectory
  · exact leading
  · intro r
    fin_cases r
    · exact initial_0
    · exact initial_1
    · exact initial_2
    · exact initial_3
  · intro r
    fin_cases r
    · exact internal_0
    · exact internal_1
    · exact internal_2
    · exact internal_3
    · exact internal_4
    · exact internal_5
    · exact internal_6
    · exact internal_7
    · exact internal_8
    · exact internal_9
    · exact internal_10
    · exact internal_11
    · exact internal_12
    · exact internal_13
  · intro r
    fin_cases r
    · exact final_0
    · exact final_1
    · exact final_2
    · exact final_3

theorem node_base :
    AppendNode.frozenEmpty (K := ZMod P) 14 =
      nodeCompress (AppendNode.frozenEmpty (K := ZMod P) 13)
        (AppendNode.frozenEmpty (K := ZMod P) 13) := by
  have hinput : (fun l : Fin 16 =>
    if h : l.val < 8 then AppendNode.frozenEmpty (K := ZMod P) 13 ⟨l.val, h⟩
    else if l.val = 15 then
      AppendNode.frozenEmpty (K := ZMod P) 13 7 - (1051521018 : ZMod P)
    else AppendNode.frozenEmpty (K := ZMod P) 13 ⟨l.val - 8, by omega⟩) = s0 := by
    unfold AppendNode.frozenEmpty emptyRootsNat
    decide
  have hout : digestOf s23 = AppendNode.frozenEmpty (K := ZMod P) 14 := by
    unfold AppendNode.frozenEmpty emptyRootsNat
    decide
  unfold nodeCompress
  rw [hinput, permutation]
  exact hout.symm

#print axioms permutation
#print axioms node_base
end AspisR1.EmptyRoot14Check
