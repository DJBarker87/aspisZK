import AspisR1TerminalDigestBindingCandidate.Source
import AspisR1TerminalDigestBindingCandidate.Exact
import OccupancyRangeTraversal
import SelectorExpansionCorrectness
import ExtractedMaskQM31Exact

set_option autoImplicit false
namespace AspisR1TerminalDigestBindingCandidate.LoopExact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate
open AspisR1TerminalDigestBindingCandidate.Exact

abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Range := core.ops.range.Range Usize

def cellAt (a : Array QM 8#usize) (j : Nat) : QM :=
  if h : j < 8 then a.val[j]'(by simpa [a.property] using h)
  else field.QM31.ZERO

def expectedAt (a : Array M31 8#usize) (j : Nat) : M31 :=
  if h : j < 8 then a.val[j]'(by simpa [a.property] using h)
  else field.M31.ZERO

def openedAt (a : Array QM 16#usize) (j : Nat) : QM :=
  (a.val[j]?).getD field.QM31.ZERO

def targetValue (expected : Array M31 8#usize) (rightTweak : Bool) (j : Nat) : Nat :=
  if h : j < 8 then
    if rightTweak = true ∧ j = 7 then
      ((expected.val[j]'(by simpa [expected.property] using h)).val +
        poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK.val) %
        AspisR1.ExtractedMaskTowerAdd.P
    else (expected.val[j]'(by simpa [expected.property] using h)).val
  else 0

def laneValue (opened : Array QM 16#usize) (start : Usize)
    (expected : Array M31 8#usize) (rightTweak : Bool) (j : Nat) : ExactQM :=
  AspisR1.ExtractedMaskQM31Exact.decode (openedAt opened (start.val + j)) -
    (targetValue expected rightTweak j : ExactQM)

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

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

private theorem cellAt_set {a : Array QM 8#usize} {i : Usize} {x : QM}
    (hi : i.val < 8) (j : Nat) :
    cellAt (a.set i x) j = if j = i.val then x else cellAt a j := by
  by_cases hj : j < 8
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

private theorem offset_add (a b : Usize) (hsum : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, (a + b : Result Usize) = .ok c ∧ c.val = a.val + b.val := by
  have hchecked : (a + b : Result Usize) ⦃ z => z.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨c, hc, hval⟩ := WP.spec_imp_exists hchecked
  refine ⟨c, ?_, hval⟩
  change (a + b : Result Usize) = .ok c
  exact hc

/-- Exact success, canonicality and all eight decoded output cells for the
production `add_digest_binding_loop`. `hprefix` is only the processed-prefix
invariant; the caller starts at lane zero with it vacuous. -/
theorem loop_success_fuel
    (opened : Array QM 16#usize) (selector : QM)
    (initial base : Array QM 8#usize) (iter : Range) (fuel : Nat)
    (start : Usize) (expected : Array M31 8#usize) (rightTweak : Bool)
    (hend : iter.end.val = 8) (hspan : iter.start.val + fuel = 8)
    (hstart : start.val + 8 ≤ 16)
    (hopened : CanonicalArray opened) (hselector : Canonical selector)
    (hinitial : CanonicalArray initial) (hbase : CanonicalArray base)
    (hexpected : ∀ j : Fin 8, (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
      AspisR1.ExtractedMaskTowerAdd.P)
    (hprefix : ∀ j : Fin 8, j.val < iter.start.val →
      AspisR1.ExtractedMaskQM31Exact.decode (cellAt base j.val) =
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) +
          AspisR1.ExtractedMaskQM31Exact.decode selector *
            laneValue opened start expected rightTweak j.val)
    (hunchanged : ∀ j : Fin 8, iter.start.val ≤ j.val →
      AspisR1.ExtractedMaskQM31Exact.decode (cellAt base j.val) =
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val)) :
    ∃ out : Array QM 8#usize,
      add_digest_binding_loop iter base selector opened start expected rightTweak = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 8,
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) +
            AspisR1.ExtractedMaskQM31Exact.decode selector *
              laneValue opened start expected rightTweak j.val := by
  induction fuel generalizing iter base with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      have hiter : iter.start.val = 8 := by omega
      refine ⟨base, ?_, hbase, ?_⟩
      · change add_digest_binding_loop iter base selector opened start expected rightTweak = .ok base
        rw [add_digest_binding_loop.eq_def]
        simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      · intro j
        have hj : j.val < iter.start.val := by omega
        exact hprefix j hj
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hlane : iter.start.val < 8 := by omega
      obtain ⟨iter1, hnext, hiter1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 8 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 8 := by omega
      let lane := iter.start
      have hlaneVal : lane.val = iter.start.val := rfl
      have hlane8 : lane.val < 8 := by simpa [lane] using hlane
      have hbaseIndex : lane.val < (8#usize).val := by simpa using hlane8
      have houtread := index_usize_ok base lane hbaseIndex
      have hexpectIndex := index_usize_ok expected lane hbaseIndex
      let old := base.val[lane.val]'(by simpa [base.property] using hbaseIndex)
      let expectedLane := expected.val[lane.val]'(by simpa [expected.property] using hbaseIndex)
      have holdCanonical : Canonical old := hbase ⟨lane.val,hbaseIndex⟩
      have hexpectCanonical : expectedLane.val < AspisR1.ExtractedMaskTowerAdd.P := by
        simpa [expectedLane] using hexpected ⟨lane.val,hbaseIndex⟩
      obtain ⟨target, htarget, htargetCanonical, htargetValue⟩ :=
        targetAfterLane_success lane expectedLane rightTweak hlane8 hexpectCanonical
      have hstartLaneBound : start.val + lane.val ≤ Usize.max := by
        have hb : start.val + lane.val < 16 := by omega
        have hmax := Usize.cMax_bound_concrete.1
        omega
      obtain ⟨openedIndex, hoffset, hoffsetVal⟩ := offset_add start lane hstartLaneBound
      have hopenBound : openedIndex.val < (16#usize).val := by
        have h16 : (16#usize).val = 16 := by scalar_tac
        rw [hoffsetVal,h16]
        omega
      have hopenread := index_usize_ok opened openedIndex hopenBound
      let openedLane := opened.val[openedIndex.val]'(by simpa [opened.property] using hopenBound)
      have hopenCanonical : Canonical openedLane := hopened ⟨openedIndex.val,hopenBound⟩
      have htargetEq :
          target.val = targetValue expected rightTweak lane.val := by
        simp [targetValue, lane, expectedLane, htargetValue, hlane8]
      obtain ⟨lifted,difference,scaled,updated,hlift,hsub,hmul,hadd,hupdatedCanonical,hformula⟩ :=
        lane_arithmetic_exact old selector openedLane target holdCanonical hselector hopenCanonical
          (by simpa [AspisR1.ExtractedMaskTowerAdd.P,AspisR1.ExtractedMaskM31AddSub.P] using htargetCanonical)
      obtain ⟨out, hupdate, hset⟩ := update_success base lane updated hlane8
      have houtCanonical : CanonicalArray out := by
        rw [hset]
        exact set_canonical base lane updated hbase hupdatedCanonical
      have hopenedCell : openedAt opened (start.val + lane.val) = openedLane := by
        have hidx : openedIndex.val = start.val + lane.val := hoffsetVal
        have hlt : openedIndex.val < opened.val.length := by simpa [opened.property] using hopenBound
        have hget : opened.val[openedIndex.val]? = some openedLane := by
          rw [List.getElem?_eq_getElem hlt]
        rw [← hidx]
        simp [openedAt, hget]
      have holdInitial : AspisR1.ExtractedMaskQM31Exact.decode old =
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial lane.val) := by
        have hu := hunchanged ⟨lane.val, by simpa [lane] using hlane⟩ (by simp [lane])
        have hc : cellAt base lane.val = old := by simp [cellAt,old,hlane8]
        rw [hc] at hu
        exact hu
      have hformulaLane :
          AspisR1.ExtractedMaskQM31Exact.decode updated =
            AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial lane.val) +
              AspisR1.ExtractedMaskQM31Exact.decode selector *
                laneValue opened start expected rightTweak lane.val := by
        unfold laneValue
        rw [hopenedCell]
        have hformula' := hformula
        rw [htargetEq] at hformula'
        rw [holdInitial] at hformula'
        exact hformula' 
      have hprefix1 : ∀ j : Fin 8, j.val < iter1.start.val →
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
            AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) +
              AspisR1.ExtractedMaskQM31Exact.decode selector *
                laneValue opened start expected rightTweak j.val := by
        intro j hj
        by_cases heq : j.val = lane.val
        · have hjEq : j = ⟨lane.val, hlane8⟩ := Fin.ext heq
          have hcell : cellAt out lane.val = updated := by
            rw [hset,cellAt_set hlane8,if_pos rfl]
          have holdcell : cellAt base lane.val = old := by simp [cellAt,old,hlane8]
          rw [hjEq, hcell]
          exact hformulaLane
        · have hjOld : j.val < iter.start.val := by omega
          have hne : j.val ≠ lane.val := by simpa [lane] using heq
          have hcell : cellAt out j.val = cellAt base j.val := by
            rw [hset,cellAt_set hlane8,if_neg hne]
          rw [hcell]
          have hp := hprefix j hjOld
          exact hp
      have hunchanged1 : ∀ j : Fin 8, iter1.start.val ≤ j.val →
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
            AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) := by
        intro j hj
        have hne : j.val ≠ lane.val := by omega
        have hcell : cellAt out j.val = cellAt base j.val := by
          rw [hset,cellAt_set hlane8,if_neg hne]
        rw [hcell]
        exact hunchanged j (by omega)
      obtain ⟨final,hloop,hfinalCanonical,hfinalValues⟩ :=
        ih out iter1 hend1' hspan1 houtCanonical hprefix1 hunchanged1
      have hbaseRead : Array.index_usize base iter.start = .ok old := by
        simpa [lane, old] using houtread
      have hexpectRead : Array.index_usize expected iter.start = .ok expectedLane := by
        simpa [lane, expectedLane] using hexpectIndex
      have hoffsetRead : (start + iter.start : Result Usize) = .ok openedIndex := by
        simpa [lane] using hoffset
      refine ⟨final, ?_, hfinalCanonical, ?_⟩
      · change add_digest_binding_loop iter base selector opened start expected rightTweak = .ok final
        rw [add_digest_binding_loop.eq_def]
        simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
        by_cases hright : rightTweak
        · cases hinc : (lane + 1#usize : Result Usize) with
          | fail e => simp [targetAfterLane, hright, hinc] at htarget
          | div => simp [targetAfterLane, hright, hinc] at htarget
          | ok i =>
            have hloopRight : add_digest_binding_loop iter1 out selector opened start expected true = .ok final := by
              simpa [hright] using hloop
            have hincLane : (iter.start + 1#usize : Result Usize) = .ok i := by
              simpa [lane] using hinc
            by_cases hcond : i = poseidon2.DIGEST_ELEMS
            · have hm : field.M31.add expectedLane
                  poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK = .ok target := by
                simpa [targetAfterLane, hright, hinc, hcond] using htarget
              simp [hright, lane, openedLane, hincLane, hcond, hm, hexpectRead, bind_tc_ok,
                hbaseRead, hoffsetRead, hopenread, hlift, hsub, hmul, hadd,
                hupdate, hloopRight]
            · have ht : expectedLane = target := by
                simpa [targetAfterLane, hright, hinc, hcond] using htarget
              subst target
              simp [hright, lane, openedLane, hincLane, hcond, hexpectRead, bind_tc_ok,
                hbaseRead, hoffsetRead, hopenread, hlift, hsub, hmul, hadd,
                hupdate, hloopRight]
        · have ht : expectedLane = target := by
            simpa [targetAfterLane, hright] using htarget
          subst target
          have hbool : rightTweak = false := by
            cases rightTweak with
            | false => rfl
            | true => exact False.elim (hright rfl)
          have hloopFalse : add_digest_binding_loop iter1 out selector opened start expected false = .ok final := by
            simpa [hbool] using hloop
          simp [hright, lane, openedLane, hexpectRead, bind_tc_ok, hbaseRead, hoffsetRead,
            hopenread, hlift, hsub, hmul, hadd, hupdate, hloopFalse]
      · exact hfinalValues

end AspisR1TerminalDigestBindingCandidate.LoopExact
