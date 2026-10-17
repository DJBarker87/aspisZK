import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFuel
import CopyActiveMaskBasisRegroup
import ExtractedMaskQM31Exact

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

def cell {n : Usize} (a : Array QM n) (j : Fin n.val) : QM :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

def prefixContribution
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (j : Fin 7) (n : Nat) : ExactQM :=
  if hn : n < 64 then
    if (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
          (R0P.copyActiveRowMasks ⟨n, hn⟩)).val = j.val then
      AspisR1.ExtractedMaskQM31Exact.decode
        (self.high.val[n]'(by simpa [self.high.property] using hn))
    else 0
  else 0

def prefixValue
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (j : Fin 7) : Nat → ExactQM
  | 0 => 0
  | n + 1 => prefixValue self j n + prefixContribution self j n

theorem prefixValue_succ
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (j : Fin 7) (n : Nat) :
    prefixValue self j (n + 1) = prefixValue self j n + prefixContribution self j n := rfl

private theorem cell_set {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (j : Fin n.val) :
    cell (a.set i x) j = if j.val = i.val then x else cell a j := by
  unfold cell
  by_cases heq : j.val = i.val
  · simp [heq, Array.set_val_eq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq, List.getElem_set_ne, hne, heq]

theorem loop0_body_step_prefix
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (sums : Array QM 7#usize) (block : Usize) (hblock : block.val < 64)
    (hself : CanonicalArray self.high) (hsums : CanonicalArray sums)
    (hinv : ∀ j : Fin 7, AspisR1.ExtractedMaskQM31Exact.decode (cell sums j) =
      prefixValue self j block.val) :
    ∃ coordinate : Usize, ∃ hcoordinate : coordinate.val < 7,
      ∃ updated : Array QM 7#usize, ∃ block1 : Usize,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
        self sums block = .ok (.cont (updated, block1)) ∧
      UScalar.add block 1#usize = .ok block1 ∧
      CanonicalArray updated ∧
      (∀ j : Fin 7, AspisR1.ExtractedMaskQM31Exact.decode (cell updated j) =
        prefixValue self j (block.val + 1)) := by
  obtain ⟨coordinate, hcoordinate, hcoordModel, added, updated, block1,
    hbody, hinc, hadd, haddCanonical, hupdatedCanonical, hset⟩ :=
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel.loop0_body_step_model
        self sums block hblock hself hsums
  let jcoord : Fin 7 := ⟨coordinate.val, hcoordinate⟩
  let old : QM := sums.val[coordinate.val]'(by
    simpa [sums.property] using hcoordinate)
  let highCell : QM := self.high.val[block.val]'(by
    simpa [self.high.property] using hblock)
  have hold : CanonicalQM old := hsums jcoord
  have hhigh : CanonicalQM highCell := hself ⟨block.val, by
    simpa [self.high.property] using hblock⟩
  obtain ⟨added', hadd', _, hdecodeAdd⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact old highCell hold hhigh
  have haddedEq : added = added' := Result.ok.inj (hadd.symm.trans hadd')
  have hdecode : AspisR1.ExtractedMaskQM31Exact.decode added =
      AspisR1.ExtractedMaskQM31Exact.decode old +
        AspisR1.ExtractedMaskQM31Exact.decode highCell := by
    rw [haddedEq]
    exact hdecodeAdd
  have hcoordVal : (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
      (R0P.copyActiveRowMasks ⟨block.val, hblock⟩)).val = coordinate.val := by
    exact congrArg (fun x : Usize => x.val) hcoordModel.symm
  refine ⟨coordinate, hcoordinate, updated, block1, hbody, hinc,
    hupdatedCanonical, ?_⟩
  intro j
  have hcell : cell sums jcoord = old := rfl
  rw [hset, cell_set]
  by_cases heq : j.val = coordinate.val
  · have hj : j = jcoord := Fin.ext heq
    subst j
    rw [if_pos rfl, hdecode]
    have hdecodeOld : AspisR1.ExtractedMaskQM31Exact.decode old =
        prefixValue self jcoord block.val := by
      rw [← hcell]
      exact hinv jcoord
    rw [hdecodeOld, prefixValue_succ]
    have hcoordJ : (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
        (R0P.copyActiveRowMasks ⟨block.val, hblock⟩)).val = jcoord.val := by
      simpa [jcoord] using hcoordVal
    simp [prefixContribution, hblock, hcoordJ, highCell]
  · rw [if_neg heq]
    have hmodelNot : (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
        (R0P.copyActiveRowMasks ⟨block.val, hblock⟩)).val ≠ j.val := by
      intro heqModel
      apply heq
      exact heqModel.symm.trans hcoordVal
    rw [hinv j]
    simp [prefixValue, prefixContribution, hblock, hmodelNot]

#print axioms loop0_body_step_prefix
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel
