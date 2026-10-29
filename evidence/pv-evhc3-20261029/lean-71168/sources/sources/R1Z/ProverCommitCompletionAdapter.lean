import R1Z.ProverCommitTapeMeasure

/-! An exact partial-decoder adapter. It carries padding explicitly, preserves
failures, and transports each individual fibre without an assumed common cF. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTapeCompletion
open R0Z.JointView
attribute [local instance] Classical.propDecidable
variable {Input K : Type} [Field K] {F : Subfield K}

def completeDecode (decode : Input → Option (SourceTape K F))
    (input : Input × Padding K F) : Option (Tape K F) :=
  (decode input.1).map (fun s => complete s input.2)

theorem completion_failure (decode : Input → Option (SourceTape K F))
    (input : Input × Padding K F) :
    completeDecode decode input = none ↔ decode input.1 = none := by
  cases h : decode input.1 <;> simp only [completeDecode, h, Option.map_none,
    Option.map_some, Option.some_ne_none, iff_self]

theorem completion_fibre (decode : Input → Option (SourceTape K F))
    (input : Input × Padding K F) (t : Tape K F) :
    completeDecode decode input = some t ↔
      decode input.1 = some (project t) ∧ input.2 = padding t := by
  cases h : decode input.1 with
  | none => simp [completeDecode, h]
  | some s =>
    simp only [completeDecode, h, Option.map_some, Option.some.injEq]
    constructor
    · intro eq
      constructor
      · exact (project_complete s input.2).symm.trans (congrArg project eq)
      · exact (padding_complete s input.2).symm.trans (congrArg padding eq)
    · rintro ⟨hs, hp⟩
      rw [hs, hp]
      exact complete_project t

/-- A full-tape fibre has exactly the original quotient fibre, with the unique
padding value required by that output. No extra success/failure factor occurs. -/
def decodedFibreEquiv (decode : Input → Option (SourceTape K F)) (t : Tape K F) :
    {x : Input × Padding K F // completeDecode decode x = some t} ≃
      {x : Input // decode x = some (project t)} where
  toFun x := ⟨x.1.1, ((completion_fibre decode x.1 t).mp x.2).1⟩
  invFun x := ⟨(x.1, padding t), (completion_fibre decode _ t).mpr ⟨x.2, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    change (x.1.1, padding t) = x.1
    apply Prod.ext
    · rfl
    · exact ((completion_fibre decode x.1 t).mp x.2).2.symm
  right_inv _ := rfl

theorem decoded_fibre_card [Fintype Input] [Fintype K]
    (decode : Input → Option (SourceTape K F)) (t : Tape K F) :
    Fintype.card {x : Input × Padding K F // completeDecode decode x = some t} =
      Fintype.card {x : Input // decode x = some (project t)} :=
  Fintype.card_congr (decodedFibreEquiv decode t)

/-- Failure witnesses transport unchanged; completion draws no sampler words. -/
theorem completion_exhaustion (decode : Input → Option (SourceTape K F))
    (exhausted₁ exhausted₂ : Input → Prop)
    (source : ∀ x, decode x = none → exhausted₁ x ∨ exhausted₂ x)
    (input : Input × Padding K F) (failure : completeDecode decode input = none) :
    exhausted₁ input.1 ∨ exhausted₂ input.1 :=
  source input.1 ((completion_failure decode input).mp failure)

#print axioms completion_failure
#print axioms completion_fibre
#print axioms decodedFibreEquiv
#print axioms decoded_fibre_card
#print axioms completion_exhaustion
end R1Z.ProverCommitTapeCompletion
