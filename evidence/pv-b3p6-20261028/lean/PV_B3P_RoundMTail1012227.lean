import PV_B3P_RoundMStep10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def round_m_source10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) : Result β := do
  let q48 ← Array.index_usize state 12#usize
  let i12 ← Array.index_usize constants1 12#usize
  let m12 ← aspis_core.field.M31.add q48.c0.a i12
  let (q49, index_mut_back12) ← Array.index_mut_usize state 12#usize
  let state25 := index_mut_back12 { q49 with c0 := { q49.c0 with a := m12 } }
  let q50 ← Array.index_usize state25 12#usize
  let q51 ← reference_poseidon.pow5 q50
  let state26 ← Array.update state25 12#usize q51
  let q52 ← Array.index_usize state26 13#usize
  let i13 ← Array.index_usize constants1 13#usize
  let m13 ← aspis_core.field.M31.add q52.c0.a i13
  let (q53, index_mut_back13) ← Array.index_mut_usize state26 13#usize
  let state27 := index_mut_back13 { q53 with c0 := { q53.c0 with a := m13 } }
  let q54 ← Array.index_usize state27 13#usize
  let q55 ← reference_poseidon.pow5 q54
  let state28 ← Array.update state27 13#usize q55
  let q56 ← Array.index_usize state28 14#usize
  let i14 ← Array.index_usize constants1 14#usize
  let m14 ← aspis_core.field.M31.add q56.c0.a i14
  let (q57, index_mut_back14) ← Array.index_mut_usize state28 14#usize
  let state29 := index_mut_back14 { q57 with c0 := { q57.c0 with a := m14 } }
  let q58 ← Array.index_usize state29 14#usize
  let q59 ← reference_poseidon.pow5 q58
  let state30 ← Array.update state29 14#usize q59
  let q60 ← Array.index_usize state30 15#usize
  let i15 ← Array.index_usize constants1 15#usize
  let m15 ← aspis_core.field.M31.add q60.c0.a i15
  let (q61, index_mut_back15) ← Array.index_mut_usize state30 15#usize
  let state31 := index_mut_back15 { q61 with c0 := { q61.c0 with a := m15 } }
  let q62 ← Array.index_usize state31 15#usize
  let q63 ← reference_poseidon.pow5 q62
  let state32 ← Array.update state31 15#usize q63
  finish state32

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize

theorem round_m_equation10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) :
    round_m_source10_12 finish constants1 state = (round_m_group10_12 constants1 state >>= finish) := by
  unfold round_m_source10_12
  conv_rhs => simp only [round_m_group10_12,PV_B3P_Ordered227.fold,round_m_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  rcases head_3 with ⟨part_3,back_3⟩
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
  rcases head_10 with ⟨part_10,back_10⟩
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
  rcases head_17 with ⟨part_17,back_17⟩
  apply bind_equal9
  intro head_18
  apply bind_equal9
  intro head_19
  apply bind_equal9
  intro head_20
  apply bind_equal9
  intro head_21
  apply bind_equal9
  intro head_22
  apply bind_equal9
  intro head_23
  apply bind_equal9
  intro head_24
  rcases head_24 with ⟨part_24,back_24⟩
  apply bind_equal9
  intro head_25
  apply bind_equal9
  intro head_26
  apply bind_equal9
  intro head_27
  rfl

def round_m_folded10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) : Result β :=
  round_m_group10_12 constants1 state >>= finish

attribute [local irreducible] round_m_group10_12

theorem round_m_factor10_12 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) :
    round_m_source10_12 finish constants1 state = round_m_folded10_12 finish constants1 state := by
  rw [round_m_equation10_12]
  rfl

#print axioms round_m_equation10_12
#print axioms round_m_factor10_12
end PV_B3P_Binding10227
