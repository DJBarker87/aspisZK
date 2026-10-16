import TerminalDigestPublicRowExtended
import TerminalDigestBindingFrontierStep
import AspisR1TerminalDigestBindingCandidate.LoopExact

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.BranchCall
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Usize := UScalar UScalarTy.Usize
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

private def decodedDigest (a : Array QM 8#usize) : R0P.Digest ExactQM :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (cellAt a j.val)

private def decodedOpenings (a : Array QM 16#usize) : Fin 16 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode (openedAt a i.val)

/-- One actual candidate `add_digest_binding` invocation at the computed
frontier row is successful/canonical and implements the exact retained
frontier-step model. The caller proves the source row arithmetic, start, and
selected target from the actual branch operands. -/
theorem binding_call
    (pub : R0P.Public ExactQM) (o : R0P.Openings ExactQM)
    (point : Array QM 10#usize) (selectors : Selectors)
    (level : Fin 20) (row : Usize) (bitZero : Prop) [Decidable bitZero]
    (initial : Array QM 8#usize) (opened : Array QM 16#usize)
    (start : Usize) (expected : Array M31 8#usize) (rightTweak : Bool)
    (hrowBound : row.val < 1024)
    (hrow : row.val = (34 + level.val) * 16 + if bitZero then 0 else 12)
    (hbitZero : bitZero ↔ R0P.digestBitZero pub level)
    (hright : rightTweak = true ↔ bitZero)
    (hstartVal : start.val = if rightTweak then 8 else 0)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hinitial : CanonicalArray initial)
    (hopened : CanonicalArray opened) (hexpected : ∀ j : Fin 8,
      (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
        AspisR1.ExtractedMaskTowerAdd.P)
    (hopenedModel : decodedOpenings opened = o.z)
    (htargetModel : ∀ j : Fin 8,
      (targetValue expected rightTweak j.val : ExactQM) =
        R0P.digestTarget pub (.frontier level) j) :
    ∃ (q : QM) (out : Array QM 8#usize),
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok q ∧
      Canonical q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q =
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
          (R0P.digestRow pub (.frontier level)) ∧
      AspisR1TerminalDigestBindingCandidate.add_digest_binding
        initial q opened start expected rightTweak = .ok out ∧
      CanonicalArray out ∧
      decodedDigest out = AspisR1TerminalDigestPublicLoop.Model.frontierStep
        pub o (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        (decodedDigest initial) level := by
  have hrowModel := AspisR1TerminalDigestPublicLoop.Row.frontier_source_row
    pub point selectors level row bitZero hrowBound hrow hbitZero hpoint hbox
  have hstartLt : start.val < 9 := by
    by_cases hr : rightTweak
    · have hs : start.val = 8 := by simpa [hr] using hstartVal
      rw [hs]
      omega
    · have hs : start.val = 0 := by simpa [hr] using hstartVal
      rw [hs]
      omega
  have hstartModel : (⟨start.val, hstartLt⟩ : Fin 9) = R0P.digestStart pub (.frontier level) := by
    apply Fin.ext
    by_cases hr : rightTweak
    · have hb : bitZero := (hright.mp hr)
      have hm : R0P.digestBitZero pub level := hbitZero.mp hb
      have hs : start.val = 8 := by simpa [hr] using hstartVal
      simp only [R0P.digestStart]
      rw [if_pos hm]
      exact hs
    · have hb : ¬ bitZero := by
        intro hz
        exact hr (hright.mpr hz)
      have hm : ¬ R0P.digestBitZero pub level := (not_congr hbitZero).mp hb
      have hs : start.val = 0 := by simpa [hr] using hstartVal
      simp only [R0P.digestStart]
      rw [if_neg hm]
      exact hs
  obtain ⟨q, hrowRun, hqcan, hrowValue⟩ := hrowModel
  have hrowValue' : AspisR1.ExtractedMaskQM31Exact.decode q =
      (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        (R0P.digestRow pub (.frontier level)) := hrowValue
  have hstartBound : start.val + 8 ≤ 16 := by
    by_cases hr : rightTweak
    · have hs : start.val = 8 := by simpa [hr] using hstartVal
      rw [hs]
    · have hs : start.val = 0 := by simpa [hr] using hstartVal
      rw [hs]
      omega
  obtain ⟨out, hrun, houtcan, hmodel⟩ :=
    AspisR1TerminalDigestPublicLoop.binding_is_frontier_step
      pub o (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
      level initial q opened start expected rightTweak
      hstartBound hinitial hqcan hopened hexpected hrowValue' hopenedModel hstartModel htargetModel
  have hmodel' : decodedDigest out = AspisR1TerminalDigestPublicLoop.Model.frontierStep
      pub o (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        (decodedDigest initial) level := by
    exact hmodel
  exact ⟨q, out, hrowRun, hqcan, hrowValue', hrun, houtcan, hmodel'⟩

#print axioms binding_call
end AspisR1TerminalDigestPublicLoop.BranchCall
