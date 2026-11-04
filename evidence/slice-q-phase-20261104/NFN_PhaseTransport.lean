import AspisR1PublicPreparation.Types
import CurrentCompactFirstCompositionV1
set_option autoImplicit false
namespace NFN_PhaseTransport
abbrev Legacy := AspisR1PublicPreparation.FirstCaller.Phase
abbrev Owned := AspisR1PublicPreparation.verifier.Phase
def forward : Legacy → Owned
 | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart x => .SemanticPart x
 | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle x => .Merkle x
 | .Query x => .Query x | .QueryPart x y => .QueryPart x y
 | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final
def backward : Owned → Legacy
 | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart x => .SemanticPart x
 | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle x => .Merkle x
 | .Query x => .Query x | .QueryPart x y => .QueryPart x y
 | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final
theorem legacy_roundtrip (p : Legacy) : backward (forward p) = p := by cases p <;> rfl
theorem owner_roundtrip (p : Owned) : forward (backward p) = p := by cases p <;> rfl
def observer {R : Type} (f : Option (Legacy → R)) : Option (Owned → R) :=
 f.map (fun g p => g (backward p))
theorem observer_none {R : Type} : observer (R:=R) none = none := rfl
theorem observer_some {R : Type} (f : Legacy → R) (p : Legacy) :
 observer (some f) = some (fun p => f (backward p)) ∧
 (f (backward (forward p))) = f p := ⟨rfl,congrArg f (legacy_roundtrip p)⟩
#print axioms legacy_roundtrip
#print axioms owner_roundtrip
#print axioms observer_none
#print axioms observer_some
end NFN_PhaseTransport
