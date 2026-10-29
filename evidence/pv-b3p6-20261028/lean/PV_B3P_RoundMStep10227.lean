import PV_B3P_RoundQStep10227
import PV_B3P_P227_05
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def round_m_step10 (constants1 : Array U32 16#usize) (state : RoundState10) (index : Usize) : Result RoundState10 := do
  let q ← Array.index_usize state index
  let i ← Array.index_usize constants1 index
  let m ← aspis_core.field.M31.add q.c0.a i
  let (q1, index_mut_back) ← Array.index_mut_usize state index
  let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
  let q2 ← Array.index_usize state1 index
  let q3 ← reference_poseidon.pow5 q2
  let state2 ← Array.update state1 index q3
  .ok state2

def round_m_group10_00 (constants1 : Array U32 16#usize) (state : RoundState10) : Result RoundState10 :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize] state

def round_m_group10_04 (constants1 : Array U32 16#usize) (state : RoundState10) : Result RoundState10 :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [4#usize, 5#usize, 6#usize, 7#usize] state

def round_m_group10_08 (constants1 : Array U32 16#usize) (state : RoundState10) : Result RoundState10 :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [8#usize, 9#usize, 10#usize, 11#usize] state

def round_m_group10_12 (constants1 : Array U32 16#usize) (state : RoundState10) : Result RoundState10 :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [12#usize, 13#usize, 14#usize, 15#usize] state
end PV_B3P_Binding10227
