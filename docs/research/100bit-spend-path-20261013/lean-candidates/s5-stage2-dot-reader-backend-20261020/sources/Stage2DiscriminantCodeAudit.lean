import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1Stage2
theorem verifier_Error_codes (x : verifier.Error) : verifier.Error.read_discriminant x =
  match x with
  | .Parse => 0#isize
  | .Semantic => 1#isize
  | .Transcript => 2#isize
  | .Relation => 3#isize
  | .Merkle => 4#isize
  | .Query => 5#isize
  | .Checkpoint => 6#isize
  | .Allocation => 7#isize := by
  cases x <;> rfl
#print axioms verifier_Error_codes
theorem transport_Variant_codes (x : transport.Variant) : transport.Variant.read_discriminant x =
  match x with
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize := by
  cases x <;> rfl
#print axioms transport_Variant_codes
theorem multiproof_Arity_codes (x : multiproof.Arity) : multiproof.Arity.read_discriminant x =
  match x with
  | .Two => 0#isize
  | .Eight => 1#isize := by
  cases x <;> rfl
#print axioms multiproof_Arity_codes
theorem verifier_Phase_codes (x : verifier.Phase) : verifier.Phase.read_discriminant x =
  match x with
  | .Parsed => 0#isize
  | .Semantic => 1#isize
  | .SemanticPart _ => 2#isize
  | .Prepare => 3#isize
  | .CheckpointRead => 4#isize
  | .Merkle _ => 5#isize
  | .Query _ => 6#isize
  | .QueryPart _ _ => 7#isize
  | .CheckpointWrite => 8#isize
  | .Relation => 9#isize
  | .Final => 10#isize := by
  cases x <;> rfl
#print axioms verifier_Phase_codes
end AspisR1Stage2
