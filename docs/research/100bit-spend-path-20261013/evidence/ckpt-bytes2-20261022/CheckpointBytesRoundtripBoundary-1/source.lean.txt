import OraclePortCkptAbiCodec

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesRoundtripBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5

/-- A fully typed C5 state with canonical field values but repeated queries.
C5's type enforces field and query ranges, not query distinctness. -/
def repeated : Prepared where
  state := fun _ => 0
  roots := fun _ _ => 0
  gamma := 0
  kappa := 0
  alpha := fun _ => 0
  rho := 0
  queries := fun _ => 0
  semanticAlpha := fun _ => 0
  coordinates := fun _ => 0
  claim := 0

def saved : QueryAccumulator.State K E := ⟨fun _ => 0,0,0,10⟩

/-- Field-canonical C5 inputs alone cannot satisfy the unqualified checkpoint
roundtrip request. The duplicate query rejection precedes physical allocation. -/
theorem canonical_repeated_rejected (H : Bytes → State) (stored pub : Bytes) :
    OraclePortCkptAbiCodec.decode (encode H stored pub repeated saved) = none := by
  exact OraclePortCkptAbiCodec.repeated_query_rejected H stored pub repeated saved rfl
    (0 : Fin 22) (1 : Fin 22) (by decide) rfl

theorem no_unqualified_roundtrip (H : Bytes → State) (stored pub : Bytes) :
    ¬ ∀ (p : Prepared) (a : QueryAccumulator.State K E), a.next = 10 →
      OraclePortCkptAbiCodec.decode (encode H stored pub p a) = some (p,a) := by
  intro all
  have impossible := all repeated saved rfl
  rw [canonical_repeated_rejected] at impossible
  cases impossible

#print axioms canonical_repeated_rejected
#print axioms no_unqualified_roundtrip
end AspisR1.CheckpointBytesRoundtripBoundary
end
