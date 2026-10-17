import PoseidonLeadingSourceDeclarationsV5
import AspisR1.PoseidonM31ConstantPow5
import ExtractedMaskHornerStep

/-! Actual per-index source body of both M31-constant full-round loops.
The checked mutable-index closure and second write are not assumed to equal
an abstract update: they are derived from the Aeneas array specifications. -/
set_option autoImplicit false
namespace AspisR1.PoseidonFullRoundCellStep
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev P := AspisR1.PoseidonM31ConstantPow5.P
abbrev State := Array QM 16#usize
abbrev Constants := Array U32 16#usize

def cell {α : Type} {N : Usize} (a : Array α N) (i : Fin N.val) : α :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
def CanonicalState (a : State) : Prop := ∀ i : Fin 16, Canonical (cell a i)
def CanonicalConstants (a : Constants) : Prop := ∀ i : Fin 16, (cell a i).val < P

def runStep (state : State) (constants1 : Constants) (lane : Usize) : Result State := do
  let q ← Array.index_usize state lane
  let i ← Array.index_usize constants1 lane
  let m ← field.M31.add q.c0.a i
  let (q1, back) ← Array.index_mut_usize state lane
  let state1 := back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)
  let q2 ← Array.index_usize state1 lane
  let q3 ← state_only_poseidon.pow5 q2
  Array.update state1 lane q3

theorem cell_set {α : Type} {N : Usize} (a : Array α N) (i : Usize)
    (x : α) (j : Fin N.val) :
    cell (a.set i x) j = if j.val = i.val then x else cell a j := by
  unfold cell
  by_cases heq : j.val = i.val
  · simp [heq,Array.set_val_eq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq,List.getElem_set_ne,hne,heq]

theorem set_canonical (a : State) (i : Usize) (x : QM)
    (ha : CanonicalState a) (hx : Canonical x) : CanonicalState (a.set i x) := by
  intro j
  rw [cell_set]
  split
  · exact hx
  · exact ha j

theorem set_overwrite {α : Type} {N : Usize} (a : Array α N) (i : Usize)
    (x y : α) : (a.set i x).set i y = a.set i y := by
  apply Subtype.ext
  simp only [Array.set_val_eq,List.set_set]

theorem runStep_success (state : State) (constants1 : Constants)
    (lane : Usize) (hlane : lane.val < 16)
    (hstate : CanonicalState state) (hconstants : CanonicalConstants constants1) :
    ∃ value : QM, runStep state constants1 lane = .ok (state.set lane value) ∧
      Canonical value ∧ CanonicalState (state.set lane value) ∧
      Decode value = R0P.poseidonPow5
        (Decode (cell state ⟨lane.val,hlane⟩) + ((cell constants1 ⟨lane.val,hlane⟩).val : Exact)) ∧
      ∀ j : Fin 16, Decode (cell (state.set lane value) j) =
        if j.val = lane.val then R0P.poseidonPow5
          (Decode (cell state ⟨lane.val,hlane⟩) + ((cell constants1 ⟨lane.val,hlane⟩).val : Exact))
        else Decode (cell state j) := by
  let index : Fin 16 := ⟨lane.val,hlane⟩
  let q := cell state index
  let c := cell constants1 index
  have hb : lane.val < (16#usize).val := by simpa using hlane
  have hread : Array.index_usize state lane = .ok q := by
    simpa only [q,cell,index] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state lane hb
  have hconstant : Array.index_usize constants1 lane = .ok c := by
    simpa only [c,cell,index] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok constants1 lane hb
  obtain ⟨value,hcell,hvalueCan,hvalueDec⟩ :=
    AspisR1.PoseidonM31ConstantPow5.source_success q c (hstate index) (hconstants index)
  obtain ⟨m,hm,hpow⟩ : ∃ m : field.M31, field.M31.add q.c0.a c = .ok m ∧
      state_only_poseidon.pow5 (AspisR1.PoseidonM31ConstantPow5.updated q m) = .ok value := by
    cases hm : field.M31.add q.c0.a c with
    | ok m =>
      refine ⟨m,rfl,?_⟩
      simpa only [AspisR1.PoseidonM31ConstantPow5.source,hm,bind_tc_ok] using hcell
    | fail e =>
      simp only [AspisR1.PoseidonM31ConstantPow5.source,hm,bind_tc_fail] at hcell
      cases hcell
    | div =>
      simp only [AspisR1.PoseidonM31ConstantPow5.source,hm,bind_tc_div] at hcell
      cases hcell
  have hmut : Array.index_mut_usize state lane = .ok (q, fun x => state.set lane x) := by
    simp only [Array.index_mut_usize,hread,bind_tc_ok]
  let updatedQ := AspisR1.PoseidonM31ConstantPow5.updated q m
  let state1 := state.set lane updatedQ
  have hreadAgain : Array.index_usize state1 lane = .ok updatedQ := by
    rw [AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state1 lane hb]
    congr 1
    change (state.val.set lane.val updatedQ)[lane.val]'_ = updatedQ
    exact List.getElem_set_self (by simpa [state.property] using hb)
  obtain ⟨out,hupdate,hset⟩ := WP.spec_imp_exists
    (Array.update_spec state1 lane value (by simpa [state1,state.property] using hb))
  have hupdate' : Array.update state1 lane value = .ok (state.set lane value) := by
    rw [hupdate,hset]
    change Result.ok ((state.set lane updatedQ).set lane value) = Result.ok (state.set lane value)
    rw [set_overwrite]
  have hstep : runStep state constants1 lane = .ok (state.set lane value) := by
    simp only [runStep,hread,hconstant,bind_tc_ok,hm,hmut]
    change (do
      let q2 ← Array.index_usize state1 lane
      let q3 ← state_only_poseidon.pow5 q2
      Array.update state1 lane q3) = _
    simp only [hreadAgain,bind_tc_ok,updatedQ,hpow,hupdate']
  change Decode value = R0P.poseidonPow5 (Decode q + (c.val : Exact)) at hvalueDec
  dsimp only [q,c,index] at hvalueDec
  refine ⟨value,hstep,hvalueCan,set_canonical state lane value hstate hvalueCan,hvalueDec,?_⟩
  intro j
  rw [cell_set]
  by_cases hj : j.val = lane.val
  · simp only [if_pos hj]
    exact hvalueDec
  · simp only [if_neg hj]

#print axioms cell_set
#print axioms set_canonical
#print axioms set_overwrite
#print axioms runStep_success
end AspisR1.PoseidonFullRoundCellStep
