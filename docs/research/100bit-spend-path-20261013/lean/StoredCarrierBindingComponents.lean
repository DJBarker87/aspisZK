import OraclePortRuntimeBindingC7

/-! Exact factorization of the original accepted-observation equality.
Neither component is asserted to follow from source inspection alone. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StoredCarrierBindingComponents
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7

/-- This is the carrier-byte part only, scoped to accepted observations. -/
def CarrierBytes (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) : Prop :=
  ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
    run.2.1.stored = (eval H (annotatedWith D rust (canon P))).2.1.stored

/-- The residual source/observation join includes ordered log, statement,
logical proof and acceptance. A byte digest contract cannot establish it. -/
def ObservationJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) : Prop :=
  ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
    let model := eval H (annotatedWith D rust (canon P))
    run.1 = model.1 ∧ run.2.1.statement = model.2.1.statement ∧
      run.2.1.proof = model.2.1.proof ∧ run.2.2 = model.2.2

theorem run_ext (a b : RunView)
    (hl : a.1 = b.1) (hs : a.2.1.statement = b.2.1.statement)
    (hp : a.2.1.proof = b.2.1.proof) (hb : a.2.1.stored = b.2.1.stored)
    (ha : a.2.2 = b.2.2) : a = b := by
  rcases a with ⟨la, ⟨⟨sa, pa, ba⟩, aa⟩⟩
  rcases b with ⟨lb, ⟨⟨sb, pb, bb⟩, ab⟩⟩
  dsimp only at hl hs hp hb ha
  cases hl; cases hs; cases hp; cases hb; cases ha
  rfl

/-- This is an equivalence, not an assumption discharge or weakening. -/
theorem binding_iff (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) :
    StoredCarrierBinding D rust P runtime ↔
      CarrierBytes D rust P runtime ∧ ObservationJoin D rust P runtime := by
  constructor
  · intro h
    constructor
    · intro H run hr ha
      rw [h H run hr ha]
    · intro H run hr ha
      rw [h H run hr ha]
      exact ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨hb, ho⟩ H run hr ha
    obtain ⟨hl, hs, hp, hv⟩ := ho H run hr ha
    exact run_ext _ _ hl hs hp (hb H run hr ha) hv

#print axioms run_ext
#print axioms binding_iff
end AspisR1.StoredCarrierBindingComponents
end
