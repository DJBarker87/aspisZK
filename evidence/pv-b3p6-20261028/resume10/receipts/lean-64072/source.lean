import PV_B3P_RoundMStep10227
import PV_B3P_RoundMTail1008227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def round_m_source10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) : Result β := do
  let q16 ← Array.index_usize state 4#usize
  let i4 ← Array.index_usize constants1 4#usize
  let m4 ← aspis_core.field.M31.add q16.c0.a i4
  let (q17, index_mut_back4) ← Array.index_mut_usize state 4#usize
  let state9 := index_mut_back4 { q17 with c0 := { q17.c0 with a := m4 } }
  let q18 ← Array.index_usize state9 4#usize
  let q19 ← reference_poseidon.pow5 q18
  let state10 ← Array.update state9 4#usize q19
  let q20 ← Array.index_usize state10 5#usize
  let i5 ← Array.index_usize constants1 5#usize
  let m5 ← aspis_core.field.M31.add q20.c0.a i5
  let (q21, index_mut_back5) ← Array.index_mut_usize state10 5#usize
  let state11 := index_mut_back5 { q21 with c0 := { q21.c0 with a := m5 } }
  let q22 ← Array.index_usize state11 5#usize
  let q23 ← reference_poseidon.pow5 q22
  let state12 ← Array.update state11 5#usize q23
  let q24 ← Array.index_usize state12 6#usize
  let i6 ← Array.index_usize constants1 6#usize
  let m6 ← aspis_core.field.M31.add q24.c0.a i6
  let (q25, index_mut_back6) ← Array.index_mut_usize state12 6#usize
  let state13 := index_mut_back6 { q25 with c0 := { q25.c0 with a := m6 } }
  let q26 ← Array.index_usize state13 6#usize
  let q27 ← reference_poseidon.pow5 q26
  let state14 ← Array.update state13 6#usize q27
  let q28 ← Array.index_usize state14 7#usize
  let i7 ← Array.index_usize constants1 7#usize
  let m7 ← aspis_core.field.M31.add q28.c0.a i7
  let (q29, index_mut_back7) ← Array.index_mut_usize state14 7#usize
  let state15 := index_mut_back7 { q29 with c0 := { q29.c0 with a := m7 } }
  let q30 ← Array.index_usize state15 7#usize
  let q31 ← reference_poseidon.pow5 q30
  let state16 ← Array.update state15 7#usize q31
  let q32 ← Array.index_usize state16 8#usize
  let i8 ← Array.index_usize constants1 8#usize
  let m8 ← aspis_core.field.M31.add q32.c0.a i8
  let (q33, index_mut_back8) ← Array.index_mut_usize state16 8#usize
  let state17 := index_mut_back8 { q33 with c0 := { q33.c0 with a := m8 } }
  let q34 ← Array.index_usize state17 8#usize
  let q35 ← reference_poseidon.pow5 q34
  let state18 ← Array.update state17 8#usize q35
  let q36 ← Array.index_usize state18 9#usize
  let i9 ← Array.index_usize constants1 9#usize
  let m9 ← aspis_core.field.M31.add q36.c0.a i9
  let (q37, index_mut_back9) ← Array.index_mut_usize state18 9#usize
  let state19 := index_mut_back9 { q37 with c0 := { q37.c0 with a := m9 } }
  let q38 ← Array.index_usize state19 9#usize
  let q39 ← reference_poseidon.pow5 q38
  let state20 ← Array.update state19 9#usize q39
  let q40 ← Array.index_usize state20 10#usize
  let i10 ← Array.index_usize constants1 10#usize
  let m10 ← aspis_core.field.M31.add q40.c0.a i10
  let (q41, index_mut_back10) ← Array.index_mut_usize state20 10#usize
  let state21 := index_mut_back10 { q41 with c0 := { q41.c0 with a := m10 } }
  let q42 ← Array.index_usize state21 10#usize
  let q43 ← reference_poseidon.pow5 q42
  let state22 ← Array.update state21 10#usize q43
  let q44 ← Array.index_usize state22 11#usize
  let i11 ← Array.index_usize constants1 11#usize
  let m11 ← aspis_core.field.M31.add q44.c0.a i11
  let (q45, index_mut_back11) ← Array.index_mut_usize state22 11#usize
  let state23 := index_mut_back11 { q45 with c0 := { q45.c0 with a := m11 } }
  let q46 ← Array.index_usize state23 11#usize
  let q47 ← reference_poseidon.pow5 q46
  let state24 ← Array.update state23 11#usize q47
  let q48 ← Array.index_usize state24 12#usize
  let i12 ← Array.index_usize constants1 12#usize
  let m12 ← aspis_core.field.M31.add q48.c0.a i12
  let (q49, index_mut_back12) ← Array.index_mut_usize state24 12#usize
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

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize round_m_source10_08

theorem round_m_equation10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) :
    round_m_source10_04 finish constants1 state = (round_m_group10_04 constants1 state >>= round_m_source10_08 finish constants1) := by
  unfold round_m_source10_04
  conv_rhs => simp only [round_m_group10_04,PV_B3P_Ordered227.fold,round_m_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
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
  unfold round_m_source10_08
  rfl

def round_m_folded10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) : Result β :=
  round_m_group10_04 constants1 state >>= round_m_folded10_08 finish constants1

attribute [local irreducible] round_m_group10_04

theorem round_m_factor10_04 {β : Type} (finish : RoundState10 → Result β) (constants1 : Array U32 16#usize) (state : RoundState10) :
    round_m_source10_04 finish constants1 state = round_m_folded10_04 finish constants1 state := by
  rw [round_m_equation10_04]
  change (round_m_group10_04 constants1 state >>= round_m_source10_08 finish constants1) = _
  apply congrArg (fun next => round_m_group10_04 constants1 state >>= next)
  funext next
  exact round_m_factor10_08 finish constants1 next

#print axioms round_m_equation10_04
#print axioms round_m_factor10_04
end PV_B3P_Binding10227
