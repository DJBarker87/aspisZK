import FJl_PreparedAtValues
import Tx2N_Fields
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ReaderFields
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
/-- Projection of source-derived SAME saved fields onto literal gamma/alpha0.
The BodyMatches premise must come from the actual saved-ten reader bridge. -/
theorem value (p : verifier.Prepared) (a : verifier.Accumulator)
    (c : Context) (data : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a (prepared c data rho q) am) :
    CheckpointBytes5Output.ofE p.gamma=data.gamma ∧
      ∀ alpha,Array.index_usize p.alpha 0#usize=ok alpha →
        CheckpointBytes5Output.ofE alpha=data.alpha0 := by
  constructor
  · rw [fields.gamma,CheckpointBytes5Output.ofE_source]
    rfl
  · intro alpha read
    have at0 : Array.index_usize p.alpha 0#usize=ok (CheckpointBytes4ReaderFields.sourceE data.alpha0) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have equal := Result.ok.inj (read.symm.trans at0)
    rw [equal,CheckpointBytes5Output.ofE_source]
#print axioms value
end AspisR1.FJl_ReaderFields
end
