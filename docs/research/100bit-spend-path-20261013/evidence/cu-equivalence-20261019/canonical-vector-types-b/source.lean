import AspisR1CanonicalDots.Types
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CanonicalDots
/-- [aspis_canonical_vector_callers::Error]
    Source: 'lib.rs', lines 4:0-4:88
    Visibility: public -/
inductive Error where
| Parse : Error
| Semantic : Error
| Transcript : Error
| Relation : Error
| Merkle : Error
| Query : Error
| Checkpoint : Error
| Allocation : Error

def Error.read_discriminant : Error→Isize
  | .Parse => 0#isize
  | .Semantic => 1#isize
  | .Transcript => 2#isize
  | .Relation => 3#isize
  | .Merkle => 4#isize
  | .Query => 5#isize
  | .Checkpoint => 6#isize
  | .Allocation => 7#isize
instance _root_.AspisR1CanonicalDots.Error.instDiscriminant :
    Aeneas.Std.Discriminant Error Isize where
  read_discriminant := Error.read_discriminant

/-- [aspis_canonical_vector_callers::new_callers::claim_dot::closure]
    Source: 'new_callers.rs', lines 8:46-8:61 -/
@[reducible]
def new_callers.claim_dot.closure := Unit

/-- [aspis_canonical_vector_callers::old_callers::claim_dot::closure]
    Source: 'old_callers.rs', lines 8:46-8:61 -/
@[reducible]
def old_callers.claim_dot.closure := Unit

end AspisR1CanonicalDots
#print axioms AspisR1CanonicalDots.Error
