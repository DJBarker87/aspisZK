import F3N_ReaderNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Y_PreparedScalars
open Aeneas Aeneas.Std Result AspisR1Stage2 OraclePortCheckpointAbiC5

theorem values (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : Prepared) (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    CheckpointBytes5Output.ofE p.claim=pm.claim ∧
    (∀ x,Array.index_usize p.alpha 0#usize=ok x → CheckpointBytes5Output.ofE x=pm.alpha 0) ∧
    (∀ x,Array.index_usize p.alpha 1#usize=ok x → CheckpointBytes5Output.ofE x=pm.alpha 1) := by
  refine ⟨?_,?_,?_⟩
  · rw [fields.claim,CheckpointBytes5Output.ofE_source]
  · intro x read
    have actual : Array.index_usize p.alpha 0#usize=ok (CheckpointBytes4ReaderFields.sourceE (pm.alpha 0)) := by
      simp [Array.index_usize,fields.alpha]
    have same := Result.ok.inj (read.symm.trans actual)
    rw [same,CheckpointBytes5Output.ofE_source]
  · intro x read
    have actual : Array.index_usize p.alpha 1#usize=ok (CheckpointBytes4ReaderFields.sourceE (pm.alpha 1)) := by
      simp [Array.index_usize,fields.alpha]
    have same := Result.ok.inj (read.symm.trans actual)
    rw [same,CheckpointBytes5Output.ofE_source]

#print axioms values
end AspisR1.F3Y_PreparedScalars
end
