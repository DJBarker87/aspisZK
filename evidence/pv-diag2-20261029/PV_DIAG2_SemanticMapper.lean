import PV_DIAG2_WireEquality
set_option autoImplicit false
noncomputable section
namespace PV_DIAG2
open Aeneas Aeneas.Std Result ProverRwFull

def isActivePole : r1_wire.Error → Bool
 | .ActivePole => true
 | _ => false

theorem active_comparison_no_payload (e : r1_wire.Error) :
 wireEqual e .ActivePole = ok (isActivePole e) := by cases e <;> rfl

theorem semantic_mapper_exact [ExternalTypes] (ops : ExternalFuns) (e : r1_wire.Error) :
 @prover.semantic_error _ (withWireEquality ops) e =
 ok (if isActivePole e then .Rejected else .Semantic) := by
 unfold prover.semantic_error
 change (do let b ← wireEqual e .ActivePole; if b then ok _ else ok _) = _
 rw [active_comparison_no_payload]
 cases isActivePole e <;> rfl

/-- Owned effect law for the complete local mapper: discriminant/Copy enum
comparison and return only. Source/derived primitive binding is recorded in
wire-equality-binding.json and semantic-mapper-binding.json. This does not
assert that a caller which produced the error was silent. -/
def semanticMapperExecution (e : r1_wire.Error) : Execution verifier.Error :=
 ⟨[],.value (if isActivePole e then .Rejected else .Semantic)⟩

theorem semantic_mapper_silent (e : r1_wire.Error) :
 (semanticMapperExecution e).effects = [] := rfl

theorem semantic_payload_irrelevant (e f : r1_wire.Error)
    (sameBranch : isActivePole e = isActivePole f) :
 semanticMapperExecution e = semanticMapperExecution f := by
 simp only [semanticMapperExecution,sameBranch]

#print axioms active_comparison_no_payload
#print axioms semantic_mapper_exact
#print axioms semantic_mapper_silent
#print axioms semantic_payload_irrelevant
end PV_DIAG2
