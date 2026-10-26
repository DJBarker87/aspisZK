import RPz7_SemanticCallSelectedCanonical
import RPz7_ExtractedSemanticRoundsReachability
/-! Actual verifier alpha canonicality: the extracted rows 15--24 round loop
returns exactly the values of its successful semantic_validated run. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical

abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev SelectedCanonical := AspisR1PublicPreparation.SemanticCallSelectedCanonical.SelectedCanonical
abbrev ToSelected := AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected

/-- Every result in a SemanticRun is canonical in the selected verifier
carrier. Each constructor is an actual successful semantic_validated call. -/
theorem run_values_canonical {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (rows : List U8)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (qs : List PublicQM)
    (hrun : AspisR1PublicPreparation.BeginCalls.SemanticRun D pre rows self after qs) :
    ∀ q, q ∈ qs → SelectedCanonical (ToSelected q) := by
  induction hrun with
  | nil =>
      intro q hq
      simp at hq
  | @cons row rows self mid after q qs record hrecord hsemantic tail ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hhead | htail
      · subst x
        exact AspisR1PublicPreparation.SemanticCallSelectedCanonical.semantic_success_selected_canonical
          D self mid record q hsemantic
      · exact ih x htail

/-- Every coordinate returned by the extracted verifier's 10-round alpha
producer is canonical. It follows from the validated verifier calls, rather
than from a prover-generated point or an input canonicality assumption. -/
theorem verifier_round_alpha_canonical {H : Type}
    (B : AspisR1PublicPreparation.RoundModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : PublicQM) (alpha : Array PublicQM 10#usize)
    (h : AspisR1PublicPreparation.RoundModel.rounds B D pre self =
      ok (.Ok (running, alpha, after))) :
    ∀ i : Fin 10,
      SelectedCanonical
        (ToSelected (alpha.val[i.val]'(by
          simpa [alpha.property] using i.isLt))) := by
  obtain ⟨qs, hrun, hqs⟩ :=
    AspisR1PublicPreparation.RoundCalls.rounds_success B D pre self after running alpha h
  have hall := run_values_canonical D pre
    AspisR1PublicPreparation.RoundCalls.rows self after qs hrun
  intro i
  have hmem : alpha.val[i.val]'(by simpa [alpha.property] using i.isLt) ∈ qs := by
    rw [hqs]
    exact List.getElem_mem _
  exact hall _ hmem

#print axioms run_values_canonical
#print axioms verifier_round_alpha_canonical
end AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical
