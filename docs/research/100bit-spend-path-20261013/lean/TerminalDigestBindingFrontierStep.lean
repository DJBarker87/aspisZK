import AspisR1TerminalDigestBindingCandidate.R0PBridge
import TerminalDigestFrontierModel

/-! A single successful digest binding equals one retained frontier fold
step, once its exact row, opened view, target, and start are identified. -/
set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact

abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev ExactQM := AspisR1TerminalDigestBindingCandidate.LoopExact.ExactQM
abbrev Canonical := AspisR1TerminalDigestBindingCandidate.LoopExact.Canonical
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev WideDigest := R0P.Digest ExactQM

private def arrayDigest (a : Array QM 8#usize) : WideDigest :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (cellAt a j.val)

private def openedModel (a : Array QM 16#usize) : Fin 16 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode (openedAt a i.val)

/-- Actual eight-lane source binding update, expressed as the model's
`digestAddBinding` at a given key. -/
theorem binding_is_frontier_step
    (pub : R0P.Public ExactQM) (o : R0P.Openings ExactQM)
    (sel : R0P.Sel ExactQM) (level : Fin 20)
    (initial : Array QM 8#usize) (selector : QM)
    (opened : Array QM 16#usize) (start : Usize)
    (expected : Array M31 8#usize) (rightTweak : Bool)
    (hstart : start.val + 8 ≤ 16)
    (hinitial : CanonicalArray initial) (hselector : Canonical selector)
    (hopened : CanonicalArray opened)
    (hexpected : ∀ j : Fin 8,
      (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
        AspisR1.ExtractedMaskTowerAdd.P)
    (hrow : AspisR1.ExtractedMaskQM31Exact.decode selector =
      sel (R0P.digestRow pub (.frontier level)))
    (hopenedModel : openedModel opened = o.z)
    (hstartModel : (⟨start.val, by omega⟩ : Fin 9) =
      R0P.digestStart pub (.frontier level))
    (htargetModel : ∀ j : Fin 8,
      (targetValue expected rightTweak j.val : ExactQM) =
        R0P.digestTarget pub (.frontier level) j) :
    ∃ out : Array QM 8#usize,
      AspisR1TerminalDigestBindingCandidate.add_digest_binding
        initial selector opened start expected rightTweak = .ok out ∧
      CanonicalArray out ∧
      arrayDigest out = AspisR1TerminalDigestPublicLoop.Model.frontierStep
        pub o sel (arrayDigest initial) level := by
  obtain ⟨out, hrun, hcanon, hvalues⟩ :=
    AspisR1TerminalDigestBindingCandidate.R0PBridge.add_digest_binding_is_r0p
      initial selector opened start expected rightTweak hstart hinitial hselector
      hopened hexpected
  refine ⟨out, hrun, hcanon, ?_⟩
  funext lane
  have hvalues' := hvalues lane
  change AspisR1.ExtractedMaskQM31Exact.decode (cellAt out lane.val) =
    R0P.digestAddBinding (arrayDigest initial)
      (AspisR1.ExtractedMaskQM31Exact.decode selector) (openedModel opened)
      (⟨start.val, by omega⟩ : Fin 9)
      (fun j : Fin 8 => (targetValue expected rightTweak j.val : ExactQM)) lane at hvalues'
  change AspisR1.ExtractedMaskQM31Exact.decode (cellAt out lane.val) =
    R0P.digestAddBinding (arrayDigest initial)
      (sel (R0P.digestRow pub (.frontier level))) o.z
      (R0P.digestStart pub (.frontier level))
      (fun j : Fin 8 => R0P.digestTarget pub (.frontier level) j) lane
  rw [hvalues', hrow, hstartModel, hopenedModel]
  congr 1
  funext j
  exact htargetModel j

#print axioms binding_is_frontier_step
end AspisR1TerminalDigestPublicLoop
