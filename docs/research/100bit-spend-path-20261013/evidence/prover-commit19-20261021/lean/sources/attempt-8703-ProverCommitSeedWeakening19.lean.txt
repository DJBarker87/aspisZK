import R1Z.ProverCommitSeedEvent19
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSeedWeakening19
open R0Z.FsStatement R1Z.ProverCommitSeedEvent19
attribute [local instance] Classical.propDecidable

/-- Proper event enlargement at any good model point whose adaptive query
suffix hits a seed point. No assumption that every adversary makes a query. -/
theorem proper_at {M : Type} (old : Fin 8 → M → Prop) (queries : M → List Entry)
    (m : M) (seed : OracleAnswer) (good : ∀ i, ¬ old i m)
    (hit : seedGuess (queries m) seed) :
    (∃ i, augmented old queries i (m,seed)) ∧ ¬ (∃ i, old i m) := by
  exact ⟨⟨0,Or.inr ⟨rfl,hit⟩⟩,fun ⟨i,hi⟩ => good i hi⟩

/-- An explicit nonempty extension, using an actual source coin query frame.
This witnesses strictness of the event constructor, not a claim that every
fixed observer or the concrete shipped prover separates the two premises. -/
theorem strict_event_witness (seed : OracleAnswer) :
    let old : Fin 8 → Unit → Prop := fun _ _ => False
    let queries : Unit → List Entry := fun _ =>
      [(ProverCommitSimulatorOracle18.address (List.ofFn seed) 0 0 0,0)]
    (∃ i, augmented old queries i ((),seed)) ∧ ¬ (∃ i, old i ()) := by
  dsimp only
  apply proper_at
  · intro i; exact id
  · exact ⟨_,List.mem_singleton_self _,source_point seed 0 0 0⟩

#print axioms proper_at
#print axioms strict_event_witness
end R1Z.ProverCommitSeedWeakening19
