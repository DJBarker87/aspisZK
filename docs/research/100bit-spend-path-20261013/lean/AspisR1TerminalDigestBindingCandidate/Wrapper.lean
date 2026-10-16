import AspisR1TerminalDigestBindingCandidate.LoopExact

set_option autoImplicit false
namespace AspisR1TerminalDigestBindingCandidate.Wrapper
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate
open AspisR1TerminalDigestBindingCandidate.LoopExact

/-- The concrete source wrapper starts the source loop at lane zero and ends at
`DIGEST_ELEMS` (eight). This specializes the fuel invariant to the caller's
initial array and exposes the exact decoded result for each digest lane. -/
theorem add_digest_binding_success
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
      ∀ j : Fin 8,
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt out j.val) =
          AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) +
            AspisR1.ExtractedMaskQM31Exact.decode selector *
              laneValue opened start expected rightTweak j.val := by
  let iter : Range := { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS }
  have hend : iter.end.val = 8 := by
    norm_num [iter, poseidon2.DIGEST_ELEMS]
  have hspan : iter.start.val + 8 = 8 := by
    norm_num [iter]
  have hprefix : ∀ j : Fin 8, j.val < iter.start.val →
      AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) =
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) +
          AspisR1.ExtractedMaskQM31Exact.decode selector *
            laneValue opened start expected rightTweak j.val := by
    intro j hj
    have : False := by simpa [iter] using hj
    exact this.elim
  have hunchanged : ∀ j : Fin 8, iter.start.val ≤ j.val →
      AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) =
        AspisR1.ExtractedMaskQM31Exact.decode (cellAt initial j.val) := by
    intro j hj
    rfl
  obtain ⟨out, hloop, houtCanonical, houtValues⟩ :=
    loop_success_fuel opened selector initial initial iter 8 start expected rightTweak
      hend hspan hstart hopened hselector hinitial hinitial hexpected hprefix hunchanged
  refine ⟨out, ?_, houtCanonical, houtValues⟩
  simpa [add_digest_binding, iter] using hloop

#print axioms AspisR1TerminalDigestBindingCandidate.LoopExact.loop_success_fuel
#print axioms add_digest_binding_success
end AspisR1TerminalDigestBindingCandidate.Wrapper
