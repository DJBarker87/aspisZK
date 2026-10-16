import PathLaneGeneratedSlice
import PathLaneArithmetic
import PreweightedGroupUpdate

/-! The literal path loop's actual checked reads, arithmetic and two writes.
The source loop factors through this step by a definitional theorem. -/
set_option autoImplicit false
namespace AspisR1.PathLaneSourceStep
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskConstants
open AspisR1.PreweightedGroupUpdate

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def cell {N : Usize} (a : Array QM N) (i : Fin N.val) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def runStep (lane : Usize) (selector : QM) (a a1 : Array QM 16#usize)
    (bit : QM) (path : Array QM 17#usize) : Result (Array QM 17#usize) := do
  let i ← 1#usize + lane
  let current ← Array.index_usize a i
  let q ← field.QM31.sub field.QM31.ONE bit
  let q1 ← field.QM31.mul selector q
  let q2 ← Array.index_usize a1 lane
  let q3 ← field.QM31.sub q2 current
  let q4 ← field.QM31.mul q1 q3
  let path1 ← Array.update path i q4
  let q5 ← field.QM31.mul selector bit
  let i1 ← AspisR1PathLaneCandidate.poseidon2.RATE + lane
  let q6 ← Array.index_usize a1 i1
  let q7 ← field.QM31.sub q6 current
  let q8 ← field.QM31.mul q5 q7
  let i2 ← 1#usize + AspisR1PathLaneCandidate.poseidon2.DIGEST_ELEMS
  let i3 ← i2 + lane
  Array.update path1 i3 q8

theorem generated_loop_step
    (iter : core.ops.range.Range Usize) (selector : QM)
    (a a1 : Array QM 16#usize) (bit : QM) (path : Array QM 17#usize) :
    AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
      iter selector a a1 bit path = (do
        let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match o with
        | none => .ok path
        | some lane =>
          let path1 ← runStep lane selector a a1 bit path
          AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
            iter1 selector a a1 bit path1) := by
  rw [AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop.eq_def]
  simp only [runStep, bind_assoc_eq]
  rfl

private theorem index_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem set_canonical {N : Usize} (a : Array QM N) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) := by
  intro j
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using j.isLt
  have hjOld : j.val < a.val.length := by simpa using j.isLt
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hjOld := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

private theorem cell_set {N : Usize} (a : Array QM N) (i : Usize) (x : QM)
    (j : Fin N.val) :
    cell (a.set i x) j = if j.val = i.val then x else cell a j := by
  unfold cell
  by_cases heq : j.val = i.val
  · simp [heq, Array.set_val_eq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq, List.getElem_set_ne, hne, heq]

theorem runStep_success
    (lane : Usize) (selector : QM) (a a1 : Array QM 16#usize)
    (bit : QM) (path : Array QM 17#usize)
    (hlane : lane.val < 8) (hs : Canonical selector) (hb : Canonical bit)
    (ha : CanonicalArray a) (ha1 : CanonicalArray a1) (hp : CanonicalArray path) :
    ∃ out, runStep lane selector a a1 bit path = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 17, decode (cell out j) =
        if j.val = 1 + lane.val then
          decode selector * (1 - decode bit) *
            (decode (cell a1 ⟨lane.val, by change lane.val < 16; omega⟩) -
              decode (cell a ⟨1 + lane.val, by change 1 + lane.val < 16; omega⟩))
        else if j.val = 9 + lane.val then
          decode selector * decode bit *
            (decode (cell a1 ⟨8 + lane.val, by change 8 + lane.val < 16; omega⟩) -
              decode (cell a ⟨1 + lane.val, by change 1 + lane.val < 16; omega⟩))
        else decode (cell path j) := by
  have hs1 : (1#usize + lane : Result Usize) ⦃ r => r.val = 1 + lane.val ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have hs8 : (8#usize + lane : Result Usize) ⦃ r => r.val = 8 + lane.val ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  have hs9 : (9#usize + lane : Result Usize) ⦃ r => r.val = 9 + lane.val ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists hs1
  obtain ⟨i1, hi1, hi1v⟩ := WP.spec_imp_exists hs8
  obtain ⟨i3, hi3, hi3v⟩ := WP.spec_imp_exists hs9
  have hadd18 : (1#usize + 8#usize : Result Usize) = .ok 9#usize := by
    have hspec : (1#usize + 8#usize : Result Usize) ⦃ r => r.val = 9 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists hspec
    have heq : r = 9#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    simpa only [heq] using hr
  have hib : i.val < 16 := by omega
  have hi1b : i1.val < 16 := by omega
  let current := cell a ⟨i.val, by change i.val < 16; exact hib⟩
  let left := cell a1 ⟨lane.val, by change lane.val < 16; omega⟩
  let right := cell a1 ⟨i1.val, by change i1.val < 16; exact hi1b⟩
  have hcurrent : Canonical current := ha ⟨i.val, by simpa [a.property] using hib⟩
  have hleft : Canonical left := ha1 ⟨lane.val, by simpa [a1.property] using (show lane.val < 16 by omega)⟩
  have hright : Canonical right := ha1 ⟨i1.val, by simpa [a1.property] using hi1b⟩
  have hreadCurrent : Array.index_usize a i = .ok current := index_ok a i (by simpa using hib)
  have hreadLeft : Array.index_usize a1 lane = .ok left := index_ok a1 lane (by change lane.val < 16; omega)
  have hreadRight : Array.index_usize a1 i1 = .ok right := index_ok a1 i1 (by simpa using hi1b)
  obtain ⟨q, hq, hcq, hvq⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact field.QM31.ONE bit one_canonical hb
  obtain ⟨q1, hq1, hcq1, hvq1⟩ := current_qm_mul_exact selector q hs hcq
  obtain ⟨q3, hq3, hcq3, hvq3⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact left current hleft hcurrent
  obtain ⟨q4, hq4, hcq4, hvq4⟩ := current_qm_mul_exact q1 q3 hcq1 hcq3
  obtain ⟨path1, hwrite1, hset1⟩ := WP.spec_imp_exists
    (Array.update_spec path i q4 (by simpa [path.property] using (show i.val < 17 by omega)))
  have hcpath1 : CanonicalArray path1 := by rw [hset1]; exact set_canonical path i q4 hp hcq4
  obtain ⟨q5, hq5, hcq5, hvq5⟩ := current_qm_mul_exact selector bit hs hb
  obtain ⟨q7, hq7, hcq7, hvq7⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact right current hright hcurrent
  obtain ⟨q8, hq8, hcq8, hvq8⟩ := current_qm_mul_exact q5 q7 hcq5 hcq7
  obtain ⟨out, hwrite2, hset2⟩ := WP.spec_imp_exists
    (Array.update_spec path1 i3 q8 (by simpa [path1.property] using (show i3.val < 17 by omega)))
  have hcout : CanonicalArray out := by rw [hset2]; exact set_canonical path1 i3 q8 hcpath1 hcq8
  have hleftValue : decode q4 = decode selector * (1 - decode bit) * (decode left - decode current) := by
    change decode q = decode field.QM31.ONE - decode bit at hvq
    change decode q3 = decode left - decode current at hvq3
    rw [hvq4, hvq1, hvq, one_decode, hvq3]
  have hrightValue : decode q8 = decode selector * decode bit * (decode right - decode current) := by
    change decode q7 = decode right - decode current at hvq7
    rw [hvq8, hvq5, hvq7]
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [runStep, AspisR1PathLaneCandidate.poseidon2.RATE, AspisR1PathLaneCandidate.poseidon2.DIGEST_ELEMS, hi,
      bind_tc_ok, hreadCurrent, hq, hq1, hreadLeft, hq3, hq4, hwrite1,
      hq5, hi1, hreadRight, hq7, hq8, hadd18, hi3, hwrite2]
  · intro j
    rw [hset2, cell_set, hset1, cell_set]
    have hneq : i.val ≠ i3.val := by omega
    by_cases hj : j.val = i.val
    · have hj3 : j.val ≠ i3.val := by omega
      have hji : j.val = 1 + lane.val := by omega
      simp only [if_pos hj, if_neg hj3, if_pos hji]
      simpa only [hiv, hi1v, current, left, cell] using hleftValue
    · by_cases hj3 : j.val = i3.val
      · have hji : j.val ≠ 1 + lane.val := by omega
        have hji3 : j.val = 9 + lane.val := by omega
        simp only [if_neg hj, if_pos hj3, if_neg hji, if_pos hji3]
        simpa only [hiv, hi1v, hi3v, current, right, cell] using hrightValue
      · have hji : j.val ≠ 1 + lane.val := by omega
        have hji3 : j.val ≠ 9 + lane.val := by omega
        simp only [if_neg hj, if_neg hj3, if_neg hji, if_neg hji3]

#print axioms generated_loop_step
#print axioms runStep_success
end
end AspisR1.PathLaneSourceStep
