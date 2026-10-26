import SCC_Physical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCD_Carrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier

/-- L162 specialized to the adopted frozen3 canonical carrier, in one world. -/
theorem canonical_stored {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (H : Bytes → State) :
    (eval H (F3T_Canon.canon (lift c P))).2.stored = (eval H P).2.stored := by
  rw [F3T_Canon.canon_eval, lift_eval]
  rfl

/-- The exact residual observer/submission association, exposed for diagnosis.
It is NOT a new trust item or a sufficient full execution refinement. -/
def ByteObservation (P : ByteProver) (runtime : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
    run.2.1.stored = (eval H P).2.stored

theorem stored_iff_observation {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (runtime : F3T_Runtime.Runtime) :
    SCC_Physical.StoredInputLaw (F3T_Canon.canon (lift c P)) runtime ↔
      ByteObservation P runtime := by
  unfold SCC_Physical.StoredInputLaw ByteObservation
  simp only [canonical_stored]

theorem observation_of_first {F C : Type} (c : DrvC_Installation.Configuration F C)
    (P : ByteProver) (runtime : F3T_Runtime.Runtime) (rust : F3T_TwoPass.Verifier)
    (first : SCC_Physical.FirstPassBinding rust (F3T_Canon.canon (lift c P)) runtime) :
    ByteObservation P runtime :=
  (stored_iff_observation c P runtime).mp (SCC_Physical.stored_of_first _ _ _ first)

#print axioms canonical_stored
#print axioms stored_iff_observation
#print axioms observation_of_first
end AspisR1.SCD_Carrier
end
