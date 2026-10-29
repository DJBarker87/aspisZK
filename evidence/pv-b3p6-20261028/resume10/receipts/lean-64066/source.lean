import PV_B3P_RoundQStep10227
import PV_B3P_RoundQTail1008227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def round_q_source10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) : Result β := do
  let q16 ← Array.index_usize state 4#usize
  let q17 ← Array.index_usize constants1 4#usize
  let q18 ← aspis_core.field.QM31.add q16 q17
  let q19 ← reference_poseidon.pow5 q18
  let state5 ← Array.update state 4#usize q19
  let q20 ← Array.index_usize state5 5#usize
  let q21 ← Array.index_usize constants1 5#usize
  let q22 ← aspis_core.field.QM31.add q20 q21
  let q23 ← reference_poseidon.pow5 q22
  let state6 ← Array.update state5 5#usize q23
  let q24 ← Array.index_usize state6 6#usize
  let q25 ← Array.index_usize constants1 6#usize
  let q26 ← aspis_core.field.QM31.add q24 q25
  let q27 ← reference_poseidon.pow5 q26
  let state7 ← Array.update state6 6#usize q27
  let q28 ← Array.index_usize state7 7#usize
  let q29 ← Array.index_usize constants1 7#usize
  let q30 ← aspis_core.field.QM31.add q28 q29
  let q31 ← reference_poseidon.pow5 q30
  let state8 ← Array.update state7 7#usize q31
  let q32 ← Array.index_usize state8 8#usize
  let q33 ← Array.index_usize constants1 8#usize
  let q34 ← aspis_core.field.QM31.add q32 q33
  let q35 ← reference_poseidon.pow5 q34
  let state9 ← Array.update state8 8#usize q35
  let q36 ← Array.index_usize state9 9#usize
  let q37 ← Array.index_usize constants1 9#usize
  let q38 ← aspis_core.field.QM31.add q36 q37
  let q39 ← reference_poseidon.pow5 q38
  let state10 ← Array.update state9 9#usize q39
  let q40 ← Array.index_usize state10 10#usize
  let q41 ← Array.index_usize constants1 10#usize
  let q42 ← aspis_core.field.QM31.add q40 q41
  let q43 ← reference_poseidon.pow5 q42
  let state11 ← Array.update state10 10#usize q43
  let q44 ← Array.index_usize state11 11#usize
  let q45 ← Array.index_usize constants1 11#usize
  let q46 ← aspis_core.field.QM31.add q44 q45
  let q47 ← reference_poseidon.pow5 q46
  let state12 ← Array.update state11 11#usize q47
  let q48 ← Array.index_usize state12 12#usize
  let q49 ← Array.index_usize constants1 12#usize
  let q50 ← aspis_core.field.QM31.add q48 q49
  let q51 ← reference_poseidon.pow5 q50
  let state13 ← Array.update state12 12#usize q51
  let q52 ← Array.index_usize state13 13#usize
  let q53 ← Array.index_usize constants1 13#usize
  let q54 ← aspis_core.field.QM31.add q52 q53
  let q55 ← reference_poseidon.pow5 q54
  let state14 ← Array.update state13 13#usize q55
  let q56 ← Array.index_usize state14 14#usize
  let q57 ← Array.index_usize constants1 14#usize
  let q58 ← aspis_core.field.QM31.add q56 q57
  let q59 ← reference_poseidon.pow5 q58
  let state15 ← Array.update state14 14#usize q59
  let q60 ← Array.index_usize state15 15#usize
  let q61 ← Array.index_usize constants1 15#usize
  let q62 ← aspis_core.field.QM31.add q60 q61
  let q63 ← reference_poseidon.pow5 q62
  let state16 ← Array.update state15 15#usize q63
  finish state16

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize round_q_source10_08

theorem round_q_equation10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) :
    round_q_source10_04 finish constants1 state = (round_q_group10_04 constants1 state >>= round_q_source10_08 finish constants1) := by
  unfold round_q_source10_04
  conv_rhs => simp only [round_q_group10_04,PV_B3P_Ordered227.fold,round_q_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  apply bind_equal9
  intro head_4
  apply bind_equal9
  intro head_5
  apply bind_equal9
  intro head_6
  apply bind_equal9
  intro head_7
  apply bind_equal9
  intro head_8
  apply bind_equal9
  intro head_9
  apply bind_equal9
  intro head_10
  apply bind_equal9
  intro head_11
  apply bind_equal9
  intro head_12
  apply bind_equal9
  intro head_13
  apply bind_equal9
  intro head_14
  apply bind_equal9
  intro head_15
  apply bind_equal9
  intro head_16
  apply bind_equal9
  intro head_17
  apply bind_equal9
  intro head_18
  apply bind_equal9
  intro head_19
  unfold round_q_source10_08
  rfl

def round_q_folded10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) : Result β :=
  round_q_group10_04 constants1 state >>= round_q_folded10_08 finish constants1

attribute [local irreducible] round_q_group10_04

theorem round_q_factor10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) :
    round_q_source10_04 finish constants1 state = round_q_folded10_04 finish constants1 state := by
  rw [round_q_equation10_04]
  change (round_q_group10_04 constants1 state >>= round_q_source10_08 finish constants1) = _
  apply congrArg (fun next => round_q_group10_04 constants1 state >>= next)
  funext next
  exact round_q_factor10_08 finish constants1 next

#print axioms round_q_equation10_04
#print axioms round_q_factor10_04
end PV_B3P_Binding10227
