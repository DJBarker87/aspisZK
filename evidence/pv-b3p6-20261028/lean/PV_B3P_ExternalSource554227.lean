import PV_B3P_ExternalGroup554227
import PV_B3P_ExternalSums554227
import PV_B3P_ExternalAdd554227
import PV_B3P_P227_03b
import PV_B3P_LinkDefinitions13227
import Lean.Elab.Tactic.AsAuxLemma
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false

def external_source554 (state : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let q0_0 ← Array.index_usize state 0#usize
  let q0_1 ← Array.index_usize state 1#usize
  let q0_2 ← Array.index_usize state 2#usize
  let q0_3 ← Array.index_usize state 3#usize
  let output0 ← external_group_source554 (Array.make 4#usize [q0_0,q0_1,q0_2,q0_3] (by simp only [List.length_cons,List.length_nil]; rfl))
  let out0_0 ← Array.index_usize output0 0#usize
  let state1 ← Array.update state 0#usize out0_0
  let out0_1 ← Array.index_usize output0 1#usize
  let state2 ← Array.update state1 1#usize out0_1
  let out0_2 ← Array.index_usize output0 2#usize
  let state3 ← Array.update state2 2#usize out0_2
  let out0_3 ← Array.index_usize output0 3#usize
  let state4 ← Array.update state3 3#usize out0_3
  let q1_0 ← Array.index_usize state4 4#usize
  let q1_1 ← Array.index_usize state4 5#usize
  let q1_2 ← Array.index_usize state4 6#usize
  let q1_3 ← Array.index_usize state4 7#usize
  let output1 ← external_group_source554 (Array.make 4#usize [q1_0,q1_1,q1_2,q1_3] (by simp only [List.length_cons,List.length_nil]; rfl))
  let out1_0 ← Array.index_usize output1 0#usize
  let state5 ← Array.update state4 4#usize out1_0
  let out1_1 ← Array.index_usize output1 1#usize
  let state6 ← Array.update state5 5#usize out1_1
  let out1_2 ← Array.index_usize output1 2#usize
  let state7 ← Array.update state6 6#usize out1_2
  let out1_3 ← Array.index_usize output1 3#usize
  let state8 ← Array.update state7 7#usize out1_3
  let q2_0 ← Array.index_usize state8 8#usize
  let q2_1 ← Array.index_usize state8 9#usize
  let q2_2 ← Array.index_usize state8 10#usize
  let q2_3 ← Array.index_usize state8 11#usize
  let output2 ← external_group_source554 (Array.make 4#usize [q2_0,q2_1,q2_2,q2_3] (by simp only [List.length_cons,List.length_nil]; rfl))
  let out2_0 ← Array.index_usize output2 0#usize
  let state9 ← Array.update state8 8#usize out2_0
  let out2_1 ← Array.index_usize output2 1#usize
  let state10 ← Array.update state9 9#usize out2_1
  let out2_2 ← Array.index_usize output2 2#usize
  let state11 ← Array.update state10 10#usize out2_2
  let out2_3 ← Array.index_usize output2 3#usize
  let state12 ← Array.update state11 11#usize out2_3
  let q3_0 ← Array.index_usize state12 12#usize
  let q3_1 ← Array.index_usize state12 13#usize
  let q3_2 ← Array.index_usize state12 14#usize
  let q3_3 ← Array.index_usize state12 15#usize
  let output3 ← external_group_source554 (Array.make 4#usize [q3_0,q3_1,q3_2,q3_3] (by simp only [List.length_cons,List.length_nil]; rfl))
  let out3_0 ← Array.index_usize output3 0#usize
  let state13 ← Array.update state12 12#usize out3_0
  let out3_1 ← Array.index_usize output3 1#usize
  let state14 ← Array.update state13 13#usize out3_1
  let out3_2 ← Array.index_usize output3 2#usize
  let state15 ← Array.update state14 14#usize out3_2
  let out3_3 ← Array.index_usize output3 3#usize
  let state16 ← Array.update state15 15#usize out3_3
  let sums ← external_sums_source554 state16
  let value0 ← Array.index_usize state16 0#usize
  let sum0 ← Array.index_usize sums 0#usize
  let result0 ← external_add_source554 value0 sum0
  let state17 ← Array.update state16 0#usize result0
  let value1 ← Array.index_usize state17 1#usize
  let sum1 ← Array.index_usize sums 1#usize
  let result1 ← external_add_source554 value1 sum1
  let state18 ← Array.update state17 1#usize result1
  let value2 ← Array.index_usize state18 2#usize
  let sum2 ← Array.index_usize sums 2#usize
  let result2 ← external_add_source554 value2 sum2
  let state19 ← Array.update state18 2#usize result2
  let value3 ← Array.index_usize state19 3#usize
  let sum3 ← Array.index_usize sums 3#usize
  let result3 ← external_add_source554 value3 sum3
  let state20 ← Array.update state19 3#usize result3
  let value4 ← Array.index_usize state20 4#usize
  let result4 ← external_add_source554 value4 sum0
  let state21 ← Array.update state20 4#usize result4
  let value5 ← Array.index_usize state21 5#usize
  let result5 ← external_add_source554 value5 sum1
  let state22 ← Array.update state21 5#usize result5
  let value6 ← Array.index_usize state22 6#usize
  let result6 ← external_add_source554 value6 sum2
  let state23 ← Array.update state22 6#usize result6
  let value7 ← Array.index_usize state23 7#usize
  let result7 ← external_add_source554 value7 sum3
  let state24 ← Array.update state23 7#usize result7
  let value8 ← Array.index_usize state24 8#usize
  let result8 ← external_add_source554 value8 sum0
  let state25 ← Array.update state24 8#usize result8
  let value9 ← Array.index_usize state25 9#usize
  let result9 ← external_add_source554 value9 sum1
  let state26 ← Array.update state25 9#usize result9
  let value10 ← Array.index_usize state26 10#usize
  let result10 ← external_add_source554 value10 sum2
  let state27 ← Array.update state26 10#usize result10
  let value11 ← Array.index_usize state27 11#usize
  let result11 ← external_add_source554 value11 sum3
  let state28 ← Array.update state27 11#usize result11
  let value12 ← Array.index_usize state28 12#usize
  let result12 ← external_add_source554 value12 sum0
  let state29 ← Array.update state28 12#usize result12
  let value13 ← Array.index_usize state29 13#usize
  let result13 ← external_add_source554 value13 sum1
  let state30 ← Array.update state29 13#usize result13
  let value14 ← Array.index_usize state30 14#usize
  let result14 ← external_add_source554 value14 sum2
  let state31 ← Array.update state30 14#usize result14
  let value15 ← Array.index_usize state31 15#usize
  let result15 ← external_add_source554 value15 sum3
  let state32 ← Array.update state31 15#usize result15
  .ok state32

attribute [local irreducible] Aeneas.Std.bind Array.index_usize Array.update
  reference_poseidon.external_group227 reference_poseidon.global_sums227 reference_poseidon.add_global227

theorem external_source_reference554 (state : Array aspis_core.field.QM31 16#usize) :
    external_source554 state = reference_poseidon.external_linear_lazy state := by
  unfold external_source554 reference_poseidon.external_linear_lazy
  as_aux_lemma =>
    apply bind_equal9
    intro q
    apply bind_equal9
    intro q1
    apply bind_equal9
    intro q2
    apply bind_equal9
    intro q3
    rw [external_group_reference554]
    apply bind_equal9
    intro output
    apply bind_equal9
    intro q4
    apply bind_equal9
    intro state1
    apply bind_equal9
    intro q5
    apply bind_equal9
    intro state2
    apply bind_equal9
    intro q6
    apply bind_equal9
    intro state3
    apply bind_equal9
    intro q7
    apply bind_equal9
    intro state4
    apply bind_equal9
    intro q8
    apply bind_equal9
    intro q9
    apply bind_equal9
    intro q10
    as_aux_lemma =>
      apply bind_equal9
      intro q11
      rw [external_group_reference554]
      apply bind_equal9
      intro output1
      apply bind_equal9
      intro q12
      apply bind_equal9
      intro state5
      apply bind_equal9
      intro q13
      apply bind_equal9
      intro state6
      apply bind_equal9
      intro q14
      apply bind_equal9
      intro state7
      apply bind_equal9
      intro q15
      apply bind_equal9
      intro state8
      apply bind_equal9
      intro q16
      apply bind_equal9
      intro q17
      apply bind_equal9
      intro q18
      apply bind_equal9
      intro q19
      rw [external_group_reference554]
      apply bind_equal9
      intro output2
      apply bind_equal9
      intro q20
      as_aux_lemma =>
        apply bind_equal9
        intro state9
        apply bind_equal9
        intro q21
        apply bind_equal9
        intro state10
        apply bind_equal9
        intro q22
        apply bind_equal9
        intro state11
        apply bind_equal9
        intro q23
        apply bind_equal9
        intro state12
        apply bind_equal9
        intro q24
        apply bind_equal9
        intro q25
        apply bind_equal9
        intro q26
        apply bind_equal9
        intro q27
        rw [external_group_reference554]
        apply bind_equal9
        intro output3
        apply bind_equal9
        intro q28
        apply bind_equal9
        intro state13
        apply bind_equal9
        intro q29
        apply bind_equal9
        intro state14
        as_aux_lemma =>
          apply bind_equal9
          intro q30
          apply bind_equal9
          intro state15
          apply bind_equal9
          intro q31
          apply bind_equal9
          intro state16
          rw [external_sums_reference554]
          apply bind_equal9
          intro sums
          apply bind_equal9
          intro q32
          apply bind_equal9
          intro a
          rw [external_add_reference554]
          apply bind_equal9
          intro q33
          apply bind_equal9
          intro state17
          apply bind_equal9
          intro q34
          apply bind_equal9
          intro a1
          rw [external_add_reference554]
          apply bind_equal9
          intro q35
          apply bind_equal9
          intro state18
          apply bind_equal9
          intro q36
          apply bind_equal9
          intro a2
          rw [external_add_reference554]
          apply bind_equal9
          intro q37
          as_aux_lemma =>
            apply bind_equal9
            intro state19
            apply bind_equal9
            intro q38
            apply bind_equal9
            intro a3
            rw [external_add_reference554]
            apply bind_equal9
            intro q39
            apply bind_equal9
            intro state20
            apply bind_equal9
            intro q40
            rw [external_add_reference554]
            apply bind_equal9
            intro q41
            apply bind_equal9
            intro state21
            apply bind_equal9
            intro q42
            rw [external_add_reference554]
            apply bind_equal9
            intro q43
            apply bind_equal9
            intro state22
            apply bind_equal9
            intro q44
            rw [external_add_reference554]
            apply bind_equal9
            intro q45
            apply bind_equal9
            intro state23
            apply bind_equal9
            intro q46
            rw [external_add_reference554]
            apply bind_equal9
            intro q47
            as_aux_lemma =>
              apply bind_equal9
              intro state24
              apply bind_equal9
              intro q48
              rw [external_add_reference554]
              apply bind_equal9
              intro q49
              apply bind_equal9
              intro state25
              apply bind_equal9
              intro q50
              rw [external_add_reference554]
              apply bind_equal9
              intro q51
              apply bind_equal9
              intro state26
              apply bind_equal9
              intro q52
              rw [external_add_reference554]
              apply bind_equal9
              intro q53
              apply bind_equal9
              intro state27
              apply bind_equal9
              intro q54
              rw [external_add_reference554]
              apply bind_equal9
              intro q55
              apply bind_equal9
              intro state28
              apply bind_equal9
              intro q56
              rw [external_add_reference554]
              apply bind_equal9
              intro q57
              apply bind_equal9
              intro state29
              as_aux_lemma =>
                apply bind_equal9
                intro q58
                rw [external_add_reference554]
                apply bind_equal9
                intro q59
                apply bind_equal9
                intro state30
                apply bind_equal9
                intro q60
                rw [external_add_reference554]
                apply bind_equal9
                intro q61
                apply bind_equal9
                intro state31
                apply bind_equal9
                intro q62
                rw [external_add_reference554]
                apply bind_equal9
                intro q63
                simp only [bind_tc_ok]

theorem external_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_external_linear_lazy external_source554 :=
  funext external_source_reference554

#print axioms external_source_reference554
#print axioms external_source_link554
end PV_B3P_Association554227
