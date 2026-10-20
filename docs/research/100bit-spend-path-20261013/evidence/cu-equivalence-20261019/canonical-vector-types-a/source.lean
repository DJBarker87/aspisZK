import AspisR1CanonicalDots.Types
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CanonicalDots
/-- [aspis_canonical_vector_callers::Error]
    Source: 'lib.rs', lines 4:0-4:88
    Visibility: public -/
@[discriminant isize]
inductive Error where
| Parse : Error
| Semantic : Error
| Transcript : Error
| Relation : Error
| Merkle : Error
| Query : Error
| Checkpoint : Error
| Allocation : Error

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
