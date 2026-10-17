import AspisR1SelectedMaskProbe.ActiveMaskBasisSourceSlice
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts
import ExtractedMaskQM31Exact
import ArrayUpdateCanonicalExact
import CopyActiveMaskBasisRegroup

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

abbrev LowIndex := {i : Usize // i.val < 16}

def lowCell (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (i : LowIndex) : QM :=
  self.low.val[i.val.val]'(by simpa [self.low.property] using i.property)

def lowItemsValue (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (items : List LowIndex) : ExactQM :=
  (items.map fun i => AspisR1.ExtractedMaskQM31Exact.decode (lowCell self i)).sum

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

def lowSumFrom
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (acc : QM) : List LowIndex → Result QM
  | [] => .ok acc
  | i :: is => do
      let x ← Array.index_usize self.low i.val
      let q ← field.QM31.add acc x
      lowSumFrom self q is

def lowSum
    (self : pool_v1.pair_forest_copy_terminal.Selectors) :
    List LowIndex → Result QM
  | [] => .fail Error.panic
  | i :: is => do
      let x ← Array.index_usize self.low i.val
      lowSumFrom self x is

def lowItems (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (items : List LowIndex) : List ExactQM :=
  items.map fun i => AspisR1.ExtractedMaskQM31Exact.decode (lowCell self i)

private theorem lowSumFrom_exact
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (acc : QM) (items : List LowIndex)
    (hacc : CanonicalQM acc) (hlow : CanonicalArray self.low) :
    ∃ out : QM, lowSumFrom self acc items = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.ExtractedMaskQM31Exact.decode acc + (lowItems self items).sum := by
  induction items generalizing acc with
  | nil =>
      refine ⟨acc, rfl, hacc, ?_⟩
      simp [lowItems]
  | cons i is ih =>
      have hread := index_usize_ok self.low i.val i.property
      let x := lowCell self i
      have hx : CanonicalQM x := hlow ⟨i.val.val, by
        simpa [self.low.property] using i.property⟩
      obtain ⟨q, hq, hqcan, hqdecode⟩ :=
        AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact acc x hacc hx
      have hread' : Array.index_usize self.low i.val = .ok x := by
        simpa [x, lowCell] using hread
      obtain ⟨out, hrun, hout, hdecode⟩ := ih q hqcan
      refine ⟨out, ?_, hout, ?_⟩
      · simp only [lowSumFrom, hread', hq, bind_tc_ok]
        exact hrun
      · rw [hdecode, hqdecode]
        simp [lowItems, List.map_cons, List.sum_cons, add_assoc, x, lowCell]

theorem lowSum_exact
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (items : List LowIndex) (hitems : items ≠ [])
    (hlow : CanonicalArray self.low) :
    ∃ out : QM, lowSum self items = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = (lowItems self items).sum := by
  cases items with
  | nil => contradiction
  | cons i is =>
      let x := lowCell self i
      have hx : CanonicalQM x := hlow ⟨i.val.val, by
        simpa [self.low.property] using i.property⟩
      have hread := index_usize_ok self.low i.val i.property
      have hread' : Array.index_usize self.low i.val = .ok x := by
        simpa [x, lowCell] using hread
      obtain ⟨out, hrun, hout, hdecode⟩ := lowSumFrom_exact self x is hx hlow
      refine ⟨out, ?_, hout, ?_⟩
      · simp only [lowSum, hread', bind_tc_ok]
        exact hrun
      · rw [hdecode]
        simp [lowItems, List.map_cons, List.sum_cons, x, lowCell]

#print axioms lowSum_exact
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum
