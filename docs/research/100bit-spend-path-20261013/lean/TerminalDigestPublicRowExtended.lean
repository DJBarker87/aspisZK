import SameBoxedRowExact
import SemanticPublicModel
import TerminalDigestPublicBranchModel
import R0P.Digest

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.Row
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Usize := UScalar UScalarTy.Usize
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

/-- A checked source row whose address is `16*(34+level)` or that address
plus twelve is exactly the retained model row for the corresponding branch. -/
theorem row_address (pub : R0P.Public ExactQM) (level : Fin 20)
    (row : Usize) (bitZero : Prop) [Decidable bitZero]
    (hrowBound : row.val < 1024)
    (hrow : row.val = (34 + level.val) * 16 + if bitZero then 0 else 12)
    (hbit : bitZero ↔ R0P.digestBitZero pub level) :
    (⟨row.val, hrowBound⟩ : Fin 1024) =
      R0P.digestRow pub (.frontier level) := by
  apply Fin.ext
  simp only [R0P.digestRow, R0P.g2Row]
  have hoff : (if bitZero then 0 else 12) =
      (if R0P.digestBitZero pub level then 0 else 12) := by
    by_cases hb : bitZero
    · simp [hb, hbit.mp hb]
    · have hnot : ¬ R0P.digestBitZero pub level := (not_congr hbit).mp hb
      simp [hb, hnot]
  rw [hrow, hoff]
  split_ifs <;> norm_num <;> omega

/-- Actual checked selector-row call at the source-derived row, with its
decoded value identified against the same boxed ten-factor point selector. -/
theorem source_row
    (point : Array QM 10#usize) (selectors : Selectors) (row : Usize)
    (hrow : row.val < 1024)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ q, pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok q ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q = pointSelector point ⟨row.val, hrow⟩ :=
  AspisR1.SameBoxedRowExact.row_success point selectors row hrow hpoint hbox

/-- The actual row operation at either frontier branch's computed address is
the exact selector input consumed by `frontierStep`. -/
theorem frontier_source_row
    (pub : R0P.Public ExactQM) (point : Array QM 10#usize)
    (selectors : Selectors) (level : Fin 20) (row : Usize)
    (bitZero : Prop) [Decidable bitZero]
    (hrowBound : row.val < 1024)
    (hrow : row.val = (34 + level.val) * 16 + if bitZero then 0 else 12)
    (hbit : bitZero ↔ R0P.digestBitZero pub level)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ q, pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok q ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q =
        pointSelector point (R0P.digestRow pub (.frontier level)) := by
  obtain ⟨q, hrun, hcan, hdecode⟩ := source_row point selectors row hrowBound hpoint hbox
  refine ⟨q, hrun, hcan, ?_⟩
  have haddress := row_address pub level row bitZero hrowBound hrow hbit
  exact hdecode.trans (congrArg (pointSelector point) haddress)

#print axioms row_address
#print axioms source_row
#print axioms frontier_source_row
end AspisR1TerminalDigestPublicLoop.Row
