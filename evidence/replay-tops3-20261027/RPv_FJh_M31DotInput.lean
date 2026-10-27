import RPv_FJh_M31DotWordStep
import RPv_FJh_InternalStateWords

/-! Exact four-coordinate body of one scalar-weight input. The coordinates
are updated independently; each uses the same processed-input budget. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotInput
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (QM Canonical cell cell_set)
open AspisR1.FJh_InternalClosureSums (Raw4)
open AspisR1.FJh_InternalStateWords (wordVec)
open AspisR1.FJh_M31DotWordStep (wide wide_value productBound step)

def Budget (raw : Raw4) (n : Nat) : Prop :=
  ∀ j : Fin 4, (cell raw j).val ≤ n*productBound

def run (raw : Raw4) (weight : QM) (value : U32) : Result Raw4 := do
  let scalar ← lift (UScalar.cast .U64 value)
  let a0 ← step raw weight.c0.a scalar 0#usize
  let a1 ← step a0 weight.c0.b scalar 1#usize
  let a2 ← step a1 weight.c1.a scalar 2#usize
  step a2 weight.c1.b scalar 3#usize

private theorem read_other (raw : Raw4) (i : Usize) (value : U64) (j : Fin 4)
    (hne : j.val ≠ i.val) : cell (raw.set i value) j = cell raw j := by
  rw [cell_set,if_neg hne]

theorem source_success (raw : Raw4) (weight : QM) (value : U32) (n : Nat)
    (hn : n ≤ 3) (hb : Budget raw n) (hw : Canonical weight)
    (hv : value.val < AspisV8R17.RawReducer.P) :
    ∃ out : Raw4, run raw weight value = .ok out ∧ Budget out (n+1) ∧
      ∀ j : Fin 4, (cell out j).val = (cell raw j).val + (cell (wordVec weight) j).val*value.val := by
  have hscalar : (wide value).val < AspisV8R17.RawReducer.P := by rw [wide_value]; exact hv
  have hbudget0 : (cell raw (0 : Fin 4)).val ≤ n*productBound := hb 0
  obtain ⟨r0,hstep0,hvalue0,hbound0⟩ := AspisR1.FJh_M31DotWordStep.source_success
    raw weight.c0.a (wide value) 0#usize (by decide) n hn hw.1.1 hscalar hbudget0
  let a0 := raw.set 0#usize r0
  have hmodel0 : r0.val = (cell raw (0 : Fin 4)).val + weight.c0.a.val*value.val := by
    change r0.val = (cell raw (0 : Fin 4)).val + weight.c0.a.val*(wide value).val at hvalue0
    rw [wide_value] at hvalue0
    exact hvalue0
  have hread1 : cell a0 (1 : Fin 4) = cell raw (1 : Fin 4) := by
    exact read_other raw 0#usize r0 (1 : Fin 4) (by decide)
  have hbudget1 : (cell a0 (1 : Fin 4)).val ≤ n*productBound := by
    rw [hread1]
    exact hb 1
  obtain ⟨r1,hstep1,hvalue1,hbound1⟩ := AspisR1.FJh_M31DotWordStep.source_success
    a0 weight.c0.b (wide value) 1#usize (by decide) n hn hw.1.2 hscalar hbudget1
  let a1 := a0.set 1#usize r1
  have hmodel1 : r1.val = (cell raw (1 : Fin 4)).val + weight.c0.b.val*value.val := by
    change r1.val = (cell a0 (1 : Fin 4)).val + weight.c0.b.val*(wide value).val at hvalue1
    rw [wide_value,hread1] at hvalue1
    exact hvalue1
  have hread2 : cell a1 (2 : Fin 4) = cell raw (2 : Fin 4) := by
    exact (read_other a0 1#usize r1 (2 : Fin 4) (by decide)).trans
      (read_other raw 0#usize r0 (2 : Fin 4) (by decide))
  have hbudget2 : (cell a1 (2 : Fin 4)).val ≤ n*productBound := by
    rw [hread2]
    exact hb 2
  obtain ⟨r2,hstep2,hvalue2,hbound2⟩ := AspisR1.FJh_M31DotWordStep.source_success
    a1 weight.c1.a (wide value) 2#usize (by decide) n hn hw.2.1 hscalar hbudget2
  let a2 := a1.set 2#usize r2
  have hmodel2 : r2.val = (cell raw (2 : Fin 4)).val + weight.c1.a.val*value.val := by
    change r2.val = (cell a1 (2 : Fin 4)).val + weight.c1.a.val*(wide value).val at hvalue2
    rw [wide_value,hread2] at hvalue2
    exact hvalue2
  have hread3 : cell a2 (3 : Fin 4) = cell raw (3 : Fin 4) := by
    exact (read_other a1 2#usize r2 (3 : Fin 4) (by decide)).trans
      ((read_other a0 1#usize r1 (3 : Fin 4) (by decide)).trans
        (read_other raw 0#usize r0 (3 : Fin 4) (by decide)))
  have hbudget3 : (cell a2 (3 : Fin 4)).val ≤ n*productBound := by
    rw [hread3]
    exact hb 3
  obtain ⟨r3,hstep3,hvalue3,hbound3⟩ := AspisR1.FJh_M31DotWordStep.source_success
    a2 weight.c1.b (wide value) 3#usize (by decide) n hn hw.2.2 hscalar hbudget3
  let a3 := a2.set 3#usize r3
  have hmodel3 : r3.val = (cell raw (3 : Fin 4)).val + weight.c1.b.val*value.val := by
    change r3.val = (cell a2 (3 : Fin 4)).val + weight.c1.b.val*(wide value).val at hvalue3
    rw [wide_value,hread3] at hvalue3
    exact hvalue3
  have hout0 : cell a3 (0 : Fin 4) = r0 := by
    simp [a3,a2,a1,a0,cell_set]
  have hout1 : cell a3 (1 : Fin 4) = r1 := by
    simp [a3,a2,a1,a0,cell_set]
  have hout2 : cell a3 (2 : Fin 4) = r2 := by
    simp [a3,a2,a1,a0,cell_set]
  have hout3 : cell a3 (3 : Fin 4) = r3 := by
    simp [a3,a2,a1,a0,cell_set]
  refine ⟨a3, ?_, ?_, ?_⟩
  · change (do
      let b0 ← step raw weight.c0.a (wide value) 0#usize
      let b1 ← step b0 weight.c0.b (wide value) 1#usize
      let b2 ← step b1 weight.c1.a (wide value) 2#usize
      step b2 weight.c1.b (wide value) 3#usize) = .ok a3
    rw [hstep0,bind_tc_ok]
    change (do
      let b1 ← step a0 weight.c0.b (wide value) 1#usize
      let b2 ← step b1 weight.c1.a (wide value) 2#usize
      step b2 weight.c1.b (wide value) 3#usize) = .ok a3
    rw [hstep1,bind_tc_ok]
    change (do
      let b2 ← step a1 weight.c1.a (wide value) 2#usize
      step b2 weight.c1.b (wide value) 3#usize) = .ok a3
    rw [hstep2,bind_tc_ok]
    exact hstep3
  · intro j
    fin_cases j
    · change (cell a3 (0 : Fin 4)).val ≤ (n+1)*productBound
      rw [hout0]
      exact hbound0
    · change (cell a3 (1 : Fin 4)).val ≤ (n+1)*productBound
      rw [hout1]
      exact hbound1
    · change (cell a3 (2 : Fin 4)).val ≤ (n+1)*productBound
      rw [hout2]
      exact hbound2
    · change (cell a3 (3 : Fin 4)).val ≤ (n+1)*productBound
      rw [hout3]
      exact hbound3
  · intro j
    fin_cases j
    · change (cell a3 (0 : Fin 4)).val = (cell raw (0 : Fin 4)).val + weight.c0.a.val*value.val
      rw [hout0]
      exact hmodel0
    · change (cell a3 (1 : Fin 4)).val = (cell raw (1 : Fin 4)).val + weight.c0.b.val*value.val
      rw [hout1]
      exact hmodel1
    · change (cell a3 (2 : Fin 4)).val = (cell raw (2 : Fin 4)).val + weight.c1.a.val*value.val
      rw [hout2]
      exact hmodel2
    · change (cell a3 (3 : Fin 4)).val = (cell raw (3 : Fin 4)).val + weight.c1.b.val*value.val
      rw [hout3]
      exact hmodel3

#print axioms source_success
end AspisR1.FJh_M31DotInput
