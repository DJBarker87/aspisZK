import ExtractedVerifyFinishReachability
import SemanticRoundAlphaSelectedCanonical
import SelectorExpansionCorrectness

/-! The alpha returned by the actual successful finish is the very alpha
produced by the ten semantic-round calls and passed to the terminal caller.
The underlying round source correspondence is bounded by the pinned
`r1_semantic.semantic_rounds` token audit; this theorem only composes the
checked reachability and canonicality facts. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualFinishAlphaSelectedCanonical

abbrev SelectedCanonical :=
  AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.SelectedCanonical
abbrev ToSelected :=
  AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.ToSelected

abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev SelectedQM := AspisR1PublicPreparation.SemanticCallSelectedCanonical.SelectedQM

/-- Coordinatewise nominal-carrier copy of exactly the array returned by
the successful semantic rounds. -/
def selectedAlpha (alpha : Array PublicQM 10#usize) : Array SelectedQM 10#usize :=
  ⟨List.map ToSelected alpha.val, by simp [alpha.property]⟩

theorem selectedAlpha_cell (alpha : Array PublicQM 10#usize) (i : Fin 10) :
    (selectedAlpha alpha).val[i.val]'(by
      simpa [(selectedAlpha alpha).property] using i.isLt) =
      ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)) := by
  simp [selectedAlpha, List.getElem_map]

theorem selectedAlpha_cell_coordinates (alpha : Array PublicQM 10#usize)
    (i : Fin 10) :
    (selectedAlpha alpha).val[i.val]'(by
      simpa [(selectedAlpha alpha).property] using i.isLt) =
      ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)) ∧
    (ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt))).c0.a.val =
      (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)).c0.a.val ∧
    (ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt))).c0.b.val =
      (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)).c0.b.val ∧
    (ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt))).c1.a.val =
      (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)).c1.a.val ∧
    (ToSelected (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt))).c1.b.val =
      (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)).c1.b.val := by
  refine ⟨selectedAlpha_cell alpha i, ?_, ?_, ?_, ?_⟩ <;> rfl

abbrev CanonicalArray {n : Usize} (a : Array SelectedQM n) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray (n := n) a

theorem alpha_selected_canonical_of_finish_success
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hfinish : AspisR1PublicPreparation.FinishModel.finish
      R B D pub pre before challenges obs = ok (.Ok out)) :
    ∀ i : Fin 10,
      SelectedCanonical
        (ToSelected (out.alpha.val[i.val]'(by
          simpa [out.alpha.property] using i.isLt))) := by
  obtain ⟨running, afterRounds, record25, record26, z0, after25, z1, after26,
      hrounds, hchallenges, hstate, htranscript, hclaims, hrecord25, hextra,
      hcircle25, hrecord26, hbeforeZ1, hcircle26, hz⟩ :=
    AspisR1PublicPreparation.FinishCalls.finish_success R B D pub pre before
      challenges obs out hfinish
  exact AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
    R D pre before afterRounds running out.alpha hrounds

/-- Canonicality for the actual array copied into the selected verifier
carrier. The same `out.alpha` is the array returned by rounds and supplied to
the terminal call; each selected cell is a literal four-coordinate copy. -/
theorem selected_alpha_array_canonical_of_finish_success
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges)
    (obs : Option (AspisR1PublicPreparation.verifier.Phase → Result Unit))
    (out : AspisR1PublicPreparation.r1_semantic.Verified H)
    (hfinish : AspisR1PublicPreparation.FinishModel.finish
      R B D pub pre before challenges obs = ok (.Ok out)) :
    CanonicalArray (selectedAlpha out.alpha) := by
  intro i
  rw [selectedAlpha_cell]
  exact alpha_selected_canonical_of_finish_success R B D pub pre before
    challenges obs out hfinish i

#print axioms alpha_selected_canonical_of_finish_success
#print axioms selected_alpha_array_canonical_of_finish_success
end AspisR1PublicPreparation.ActualFinishAlphaSelectedCanonical
