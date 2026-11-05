import VTop_Model
set_option autoImplicit false
namespace NHT_ResultPort
open Aeneas Aeneas.Std Result
abbrev SourceError := AspisR1Stage2.verifier.Error
abbrev TargetError := VTop_Stages.verifier.Error

def error : SourceError → TargetError
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def back : TargetError → SourceError
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def reply {A : Type} : core.result.Result A SourceError → core.result.Result A TargetError
 | .Ok a => .Ok a | .Err e => .Err (error e)

def action {A : Type} (m : Result (core.result.Result A SourceError)) :
 Result (core.result.Result A TargetError) := do
 let r ← m
 ok (reply r)

theorem roundtrip (e : SourceError) : back (error e)=e := by cases e <;> rfl

theorem injective : Function.Injective error := by
 intro x y h
 have same := congrArg back h
 simpa only [roundtrip] using same

theorem returned_error {A : Type} (e : SourceError) :
 action (ok (.Err e) : Result (core.result.Result A SourceError))=ok (.Err (error e)) := rfl

theorem failure {A : Type} (e : Aeneas.Std.Error) :
 action (.fail e : Result (core.result.Result A SourceError))=.fail e := rfl

theorem divergence {A : Type} :
 action (.div : Result (core.result.Result A SourceError))=.div := rfl
#print axioms roundtrip
#print axioms injective
#print axioms returned_error
#print axioms failure
#print axioms divergence
end NHT_ResultPort
