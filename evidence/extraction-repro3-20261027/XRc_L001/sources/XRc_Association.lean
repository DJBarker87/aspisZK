import AspisR1PublicPreparation.Types
set_option autoImplicit false

/- A declaration-level carrier projection only. The release enum below is an
exact declaration slice from XRc_003 Types, placed in XRc_Release to avoid
colliding with the imported cohort enum. No external template is imported,
no library is replaced, and no top imports this module. This does not bind
any missing release function body or prove complete kit association. -/
namespace XRc_Release
@[discriminant isize]
inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error
end XRc_Release

namespace XRc_Association
abbrev OldError := AspisR1PublicPreparation.verifier.Error
abbrev NewError := XRc_Release.verifier.Error

def projectError : NewError → OldError
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

def embedError : OldError → NewError
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

/-- Exact carrier obligation for the cfg-selected eight-constructor pair. -/
def VerifierErrorAssociation : Prop :=
  (∀ e : OldError, projectError (embedError e) = e) ∧
  (∀ e : NewError, embedError (projectError e) = e)

theorem verifier_error_association : VerifierErrorAssociation := by
  constructor
  · intro e; cases e <;> rfl
  · intro e; cases e <;> rfl

#print axioms verifier_error_association
end XRc_Association
