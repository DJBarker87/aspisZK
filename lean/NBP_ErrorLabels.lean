import NBG_Error
set_option autoImplicit false
namespace NBP_ErrorLabels
open NBG_Error
/-- Literal table shared by native K002-K017 and the exact log transition. -/
theorem labels (e : E) : message e =
    match e with
    | .Parse => "r1:error:Parse" | .Semantic => "r1:error:Semantic"
    | .Transcript => "r1:error:Transcript" | .Relation => "r1:error:Relation"
    | .Merkle => "r1:error:Merkle" | .Query => "r1:error:Query"
    | .Checkpoint => "r1:error:Checkpoint" | .Allocation => "r1:error:Allocation" := by
  cases e <;> rfl
#print axioms labels
#print axioms NBG_Error.transition
end NBP_ErrorLabels
