import PV_B3P_RoundQStep10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def round_q_source10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) : Result β := do
  let q48 ← Array.index_usize state 12#usize
  let q49 ← Array.index_usize constants1 12#usize
  let q50 ← aspis_core.field.QM31.add q48 q49
  let q51 ← reference_poseidon.pow5 q50
  let state13 ← Array.update state 12#usize q51
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

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize

theorem round_q_equation10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) :
    round_q_source10_12 finish constants1 state = (round_q_group10_12 constants1 state >>= finish) := by
  unfold round_q_source10_12
  conv_rhs => simp only [round_q_group10_12,PV_B3P_Ordered227.fold,round_q_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

def round_q_folded10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) : Result β :=
  round_q_group10_12 constants1 state >>= finish

attribute [local irreducible] round_q_group10_12

theorem round_q_factor10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array aspis_core.field.QM31 16#usize) (state : RoundState10) :
    round_q_source10_12 finish constants1 state = round_q_folded10_12 finish constants1 state := by
  rw [round_q_equation10_12]
  rfl

#print axioms round_q_equation10_12
#print axioms round_q_factor10_12
end PV_B3P_Binding10227
