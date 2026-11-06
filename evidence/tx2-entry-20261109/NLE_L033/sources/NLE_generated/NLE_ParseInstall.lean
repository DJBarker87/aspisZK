import NLE_AuthFold
import Op3I_ParseLaws
import NJS_Parse
set_option autoImplicit false
noncomputable section
namespace NLE_ParseInstall
open Aeneas Aeneas.Std Result VTop_Stages
/-- Explicit nominal carrier transport; no claim that independently emitted
Rust enums are definitionally the same Lean type. -/
def variant : Op3I_Source.transport.Variant → transport.Variant
 | .S1 => .S1 | .S2 => .S2 | .D => .D
def error : Op3I_Source.verifier.Error → verifier.Error
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def reply : core.result.Result Op3I_Source.transport.Variant Op3I_Source.verifier.Error →
 core.result.Result transport.Variant verifier.Error
 | .Ok value => .Ok (variant value) | .Err err => .Err (error err)
def parse (proof : Slice U8) : Result (core.result.Result transport.Variant verifier.Error) := do
 let result ← Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof
 ok (reply result)
def install (ops : Ops) : Ops := {ops with op3 := parse}
/-- The actual CLOSED parser supplies C01's proof length before common. -/
theorem success (proof : Slice U8) (value : transport.Variant)
 (returned : parse proof = ok (.Ok value)) : value = .S2 ∧ proof.val.length = 57607 := by
 unfold parse at returned
 cases h : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
 | fail err => rw [h] at returned; cases returned
 | div => rw [h] at returned; cases returned
 | ok result =>
  rw [h] at returned
  cases result with
  | Err err => cases returned
  | Ok raw =>
   have facts := Op3I_ParseLaws.source_success proof raw h
   rw [facts.1] at returned
   cases returned
   exact ⟨rfl,facts.2.1⟩
/-- The parser is the adopted source parser, not the native test oracle.
NJS_Parse.source certifies the actual frozen emission on ALL proof slices. -/
theorem emitted (proof : Slice U8) : parse proof =
 NJS_Parse.map reply (NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape
   Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof)) := by
 rw [NJS_Parse.source]
 rfl
#print success
#print emitted
#print axioms success
#print axioms emitted
end NLE_ParseInstall
