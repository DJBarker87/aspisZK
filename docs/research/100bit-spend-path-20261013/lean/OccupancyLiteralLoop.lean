import OccupancyGeneratedSlice
import OccupancyRangeTraversal
import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd
import ExtractedMaskReducerOps
import SelectorExpansionCorrectness

/-! Source proof for the eight-lane generated occupancy iterator. The result
array's exact successful execution, canonicality, and indexed decoded cells
are derived from the generated loop, its Aeneas range iterator, and the pinned
QM31 multiplication theorem. -/
set_option autoImplicit false
namespace AspisR1.OccupancyLiteralLoop

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskReducerOps

abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Range := core.ops.range.Range Usize
abbrev Loop := pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop

def cellAt (a : Array QM 12#usize) (j : Nat) : QM :=
  if h : j < 12 then a.val[j]'(by simpa [a.property] using h)
  else field.QM31.ZERO

def openedCell (opened : Array QM 16#usize) (j : Nat) : QM :=
  (opened.val[j]?).getD field.QM31.ZERO

def laneValue (opened : Array QM 16#usize) (oneMinus both : QM) (j : Nat) : ExactQM :=
  AspisR1.ExtractedMaskQM31Exact.decode both *
    (AspisR1.ExtractedMaskQM31Exact.decode oneMinus *
      AspisR1.ExtractedMaskQM31Exact.decode (openedCell opened (j - 1)))

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem usize_add_result (a b : Usize) (hsum : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, UScalar.add a b = .ok c ∧ c.val = a.val + b.val := by
  have hchecked : (a + b : Result Usize) ⦃ z => z.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨c, hc, hval⟩ := WP.spec_imp_exists hchecked
  refine ⟨c, ?_, hval⟩
  change (a + b : Result Usize) = .ok c
  exact hc

private theorem update_success {n : Usize} (a : Array QM n) (i : Usize)
    (x : QM) (hi : i.val < n.val) :
    ∃ out : Array QM n, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hr, hs⟩

private theorem set_canonical {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) := by
  intro j
  have hj0 : j.val < a.val.length := by simpa using j.isLt
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using hj0
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hj0 := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

private theorem cellAt_set {a : Array QM 12#usize} {i : Usize} {x : QM}
    (hi : i.val < 12) (j : Nat) :
    cellAt (a.set i x) j = if j = i.val then x else cellAt a j := by
  by_cases hj : j < 12
  · by_cases hEq : j = i.val
    · subst j
      simp [cellAt, hj, Array.set_val_eq]
    · have hne : i.val ≠ j := Ne.symm hEq
      have hjSet : j < (a.val.set i.val x).length := by simpa [a.property] using hj
      have hjA : j < a.val.length := by simpa [a.property] using hj
      have hcell := List.getElem_set_ne (l := a.val) (i := i.val) (j := j) hne hjSet
      simp [cellAt, hj, Array.set_val_eq, hEq, hcell, hjA]
  · have hne : j ≠ i.val := by omega
    simp [cellAt, hj, Array.set_val_eq, hne]

private theorem small_usize_bound (n : Nat) (hn : n < 32) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem offset_add (k : Nat) (hk : k < 4) (lane : Usize) (hlane : lane.val < 8) :
    ∃ out : Usize,
      UScalar.add (k#usize) lane = .ok out ∧ out.val = k + lane.val := by
  have hb : k + lane.val < 2 ^ UScalarTy.Usize.numBits := by
    apply small_usize_bound
    omega
  obtain ⟨out, hrun, hval⟩ := tryMk_success (ty := .Usize) (k + lane.val) hb
  have hk : (k#usize).val = k := by scalar_tac
  refine ⟨out, ?_, ?_⟩
  · change UScalar.add (k#usize) lane = .ok out
    simpa [UScalar.add] using hrun
  · simpa [hk] using hval

/-- A fuel-indexed theorem for the exact source iterator. `hprefix` records
only cells already processed before this invocation, so recursive calls do
not assume the desired terminal vector. -/
theorem loop_success_fuel
    (opened : Array QM 16#usize) (oneMinus both : QM)
    (initial : Array QM 12#usize) (iter : Range) (fuel : Nat)
    (hend : iter.end.val = 8) (hspan : iter.start.val + fuel = 8)
    (hopened : CanonicalArray opened) (honeMinus : Canonical oneMinus)
    (hboth : Canonical both) (hinitial : CanonicalArray initial)
    (hprefix : ∀ j : Fin 12, 3 ≤ j.val → j.val < 3 + iter.start.val →
      AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) = laneValue opened oneMinus both j.val) :
    ∃ out : Array QM 12#usize,
      Loop iter opened oneMinus initial both = .ok out ∧ CanonicalArray out ∧
      (∀ j : Fin 12,
        if 3 ≤ j.val ∧ j.val < 11 then
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) = laneValue opened oneMinus both j.val
        else AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) = AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val)) := by
  induction fuel generalizing iter initial with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hstart : iter.start.val = 8 := by omega
      refine ⟨initial, ?_, hinitial, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
          iter opened oneMinus initial both = .ok initial
        rw [pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop.eq_def]
        simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      · intro j
        by_cases hj : 3 ≤ j.val ∧ j.val < 11
        · have hproc : j.val < 3 + iter.start.val := by omega
          simpa [hj] using hprefix j (by omega) hproc
        · simp [hj]
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hlane : iter.start.val < 8 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 8 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 8 := by omega
      let lane := iter.start
      have hidx : lane.val = iter.start.val := rfl
      obtain ⟨i, hi, hiv⟩ := offset_add 2 (by decide) lane (by simpa [lane] using hlane)
      obtain ⟨i1, hi1, hi1v⟩ := offset_add 3 (by decide) lane (by simpa [lane] using hlane)
      have h16U : (16#usize).val = 16 := by scalar_tac
      have h12U : (12#usize).val = 12 := by scalar_tac
      have hiBound : i.val < (16#usize).val := by rw [hiv, h16U]; omega
      have hi1Bound : i1.val < 12 := by rw [hi1v]; omega
      have hi1BoundU : i1.val < (12#usize).val := by simpa [h12U] using hi1Bound
      have hread : Array.index_usize opened i =
          .ok (opened.val[i.val]'(by simpa [opened.property] using hiBound)) :=
        index_usize_ok opened i hiBound
      let q := opened.val[i.val]'(by simpa [opened.property] using hiBound)
      have hqcan : Canonical q := by
        apply hopened ⟨i.val, hiBound⟩
      obtain ⟨q1, hmul1, hq1can, hq1val⟩ :=
        current_qm_mul_exact oneMinus q honeMinus hqcan
      have hmul1' : field.QM31.mul oneMinus
          (opened.val[i.val]'(by simpa [opened.property] using hiBound)) = .ok q1 := by
        simpa [q] using hmul1
      obtain ⟨q2, hmul2, hq2can, hq2val⟩ :=
        current_qm_mul_exact both q1 hboth hq1can
      obtain ⟨updated, hupdate, hset⟩ := update_success initial i1 q2 hi1BoundU
      have hupdatedCan : CanonicalArray updated := by
        rw [hset]
        exact set_canonical initial i1 q2 hinitial hq2can
      have hqcell : openedCell opened (3 + lane.val - 1) = q := by
        have hidxEq : 3 + lane.val - 1 = i.val := by rw [hiv]; omega
        have hltI : i.val < opened.val.length := by simpa [opened.property] using hiBound
        have hget : opened.val[i.val]? = some q := by
          rw [List.getElem?_eq_getElem hltI]
        unfold openedCell
        rw [hidxEq, hget]
        rfl
      have hq2model : AspisR1.ExtractedMaskQM31Exact.decode q2 = laneValue opened oneMinus both (3 + lane.val) := by
        rw [hq2val, hq1val]
        simp only [laneValue, hqcell]
      have hprefix1 : ∀ j : Fin 12, 3 ≤ j.val → j.val < 3 + iter1.start.val →
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt updated j.val) = laneValue opened oneMinus both j.val := by
        intro j hjlo hjhi
        by_cases heq : j.val = 3 + lane.val
        · have hEqI1 : j.val = i1.val := by rw [hi1v]; simpa [lane] using heq
          have hcell : cellAt updated j.val = q2 := by
            rw [hset, cellAt_set hi1Bound, if_pos hEqI1]
          rw [hcell, heq]
          exact hq2model
        · have hold : j.val < 3 + iter.start.val := by omega
          have hNeI1 : j.val ≠ i1.val := by
            intro h
            apply heq
            calc
              j.val = i1.val := h
              _ = 3 + lane.val := hi1v
          have hcell : cellAt updated j.val = cellAt initial j.val := by
            rw [hset, cellAt_set hi1Bound, if_neg hNeI1]
          rw [hcell]
          exact hprefix j hjlo hold
      obtain ⟨out, hrun, houtcan, hvalues⟩ :=
        ih updated iter1 hend1' hspan1 hupdatedCan hprefix1
      have hvaluesOriginal : ∀ j : Fin 12,
          if 3 ≤ j.val ∧ j.val < 11 then
            AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) = laneValue opened oneMinus both j.val
          else AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
            AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) := by
        intro j
        by_cases hj : 3 ≤ j.val ∧ j.val < 11
        · simpa [hj] using hvalues j
        · have hneq : j.val ≠ i1.val := by
            intro h
            apply hj
            constructor
            · rw [h, hi1v]
              omega
            · rw [h, hi1v]
              have hl : lane.val < 8 := by simpa [lane] using hlane
              omega
          have hunchanged : cellAt updated j.val = cellAt initial j.val := by
            rw [hset, cellAt_set hi1Bound, if_neg hneq]
          have hval := hvalues j
          simp only [if_neg hj] at hval
          have hcalc : AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
              AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) := by
            calc
              AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
                  AspisR1.ExtractedMaskQM31Exact.decode (cellAt updated j.val) := hval
              _ = AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) :=
                congrArg AspisR1.ExtractedMaskQM31Exact.decode hunchanged
          simpa [hj] using hcalc
      refine ⟨out, ?_, houtcan, hvaluesOriginal⟩
      · change pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
          iter opened oneMinus initial both = .ok out
        rw [pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop.eq_def]
        simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
        change (do
          let i ← (UScalar.add 2#usize lane : Result Usize)
          let q ← Array.index_usize opened i
          let q1 ← field.QM31.mul oneMinus q
          let q2 ← field.QM31.mul both q1
          let i1 ← (UScalar.add 3#usize lane : Result Usize)
          let a ← Array.update initial i1 q2
          pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
            iter1 opened oneMinus a both) = .ok out
        simp only [hi, bind_tc_ok, hread, bind_tc_ok, hmul1', bind_tc_ok,
          hmul2, bind_tc_ok, hi1, bind_tc_ok, hupdate, bind_tc_ok]
        exact hrun

#print axioms loop_success_fuel
end AspisR1.OccupancyLiteralLoop
