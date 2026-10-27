import RPz7_Tx2N_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_SavedIdentities
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Decode only saved Prepared fields, before specializing the model Context. -/
theorem fields (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (h : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    CheckpointBytes5Output.ofE p.claim = pm.claim ∧
    (∀ x, Array.index_usize p.alpha 0#usize = ok x → CheckpointBytes5Output.ofE x = pm.alpha 0) ∧
    (∀ x, Array.index_usize p.alpha 1#usize = ok x → CheckpointBytes5Output.ofE x = pm.alpha 1) := by
  refine ⟨(congrArg CheckpointBytes5Output.ofE h.claim).trans
    (CheckpointBytes5Output.ofE_source pm.claim),?_,?_⟩
  · intro x hx
    have source : Array.index_usize p.alpha 0#usize =
        ok (CheckpointBytes4ReaderFields.sourceE (pm.alpha 0)) := by
      simp [Array.index_usize,h.alpha]
    exact (congrArg CheckpointBytes5Output.ofE (Result.ok.inj (hx.symm.trans source))).trans
      (CheckpointBytes5Output.ofE_source (pm.alpha 0))
  · intro x hx
    have source : Array.index_usize p.alpha 1#usize =
        ok (CheckpointBytes4ReaderFields.sourceE (pm.alpha 1)) := by
      simp [Array.index_usize,h.alpha]
    exact (congrArg CheckpointBytes5Output.ofE (Result.ok.inj (hx.symm.trans source))).trans
      (CheckpointBytes5Output.ofE_source (pm.alpha 1))

#print axioms fields
end AspisR1.SAF_SavedIdentities
end
