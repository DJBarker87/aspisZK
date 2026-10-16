import AspisR1TerminalDigestBindingCandidate.Wrapper
import R0P.Digest

set_option autoImplicit false
namespace AspisR1TerminalDigestBindingCandidate.R0PBridge
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate
open AspisR1TerminalDigestBindingCandidate.LoopExact

/-- The actual source wrapper is the R0P eight-lane digest accumulator, with
its M31 target preprocessed by the source's right-tweak branch. -/
theorem add_digest_binding_is_r0p
    (initial : Array QM 8#usize) (selector : QM)
    (opened : Array QM 16#usize) (start : Usize)
    (expected : Array M31 8#usize) (rightTweak : Bool)
    (hstart : start.val + 8 ≤ 16)
    (hinitial : CanonicalArray initial) (hselector : Canonical selector)
    (hopened : CanonicalArray opened)
    (hexpected : ∀ j : Fin 8,
      (expected.val[j.val]'(by simpa [expected.property] using j.isLt)).val <
        AspisR1.ExtractedMaskTowerAdd.P) :
    ∃ out : Array QM 8#usize,
      add_digest_binding initial selector opened start expected rightTweak = .ok out ∧
      CanonicalArray out ∧
      ∀ lane : Fin 8,
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt out lane.val) =
          R0P.digestAddBinding
            (fun j : Fin 8 => AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val))
            (AspisR1.ExtractedMaskQM31Exact.decode selector)
            (fun i : Fin 16 => AspisR1.ExtractedMaskQM31Exact.decode (openedAt opened i.val))
            (⟨start.val, by omega⟩ : Fin 9)
            (fun j : Fin 8 => (targetValue expected rightTweak j.val : ExactQM))
            lane := by
  obtain ⟨out, hsuccess, hcanonical, hvalues⟩ :=
    AspisR1TerminalDigestBindingCandidate.Wrapper.add_digest_binding_success
      initial selector opened start expected rightTweak hstart hinitial hselector hopened hexpected
  refine ⟨out, hsuccess, hcanonical, ?_⟩
  intro lane
  rw [hvalues lane]
  rfl

#print axioms add_digest_binding_is_r0p
end AspisR1TerminalDigestBindingCandidate.R0PBridge
