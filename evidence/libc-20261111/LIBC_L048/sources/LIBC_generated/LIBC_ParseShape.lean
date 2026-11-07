import LIBC_Bytes
import LIBC_ResultGraph
import LIB_VCarriers
import NJS_Parse
set_option autoImplicit false
noncomputable section
namespace LIBC_ParseShape
open Aeneas Aeneas.Std Result RSL
abbrev VErr := LIB_VCarriers.VErr
def error : Op3I_Source.verifier.Error → VErr
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def port : core.result.Result Op3I_Source.transport.Variant Op3I_Source.verifier.Error → Except VErr Unit
 | .Ok _ => .ok () | .Err e => .error (error e)
def Domain (proof : Bytes) : Prop := proof.length=57607
def model (proof : Bytes) (_ : Env) :=
 Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops (LIBC_Bytes.raw proof)
def child : Child Bytes (Except VErr Unit) :=
 ⟨Domain,fun proof => LIB_Carriers.resultGraph port (model proof) (fun _ => [])⟩
def value (proof : Bytes) (env : Env) : Except VErr Unit :=
 LIBC_ResultGraph.value port (.error .Parse) (model proof env)
theorem returns (proof : Bytes) (env : Env) :
 NND_Returned.Returns (child.law proof) env (value proof env) :=
 LIBC_ResultGraph.returns _ _ _ _ env
/-- CLOSED086 full emitted-copy equality at the SAME original byte backing. -/
theorem source (proof : Slice U8) (env : Env) :
 model (LIB_Carriers.bytes proof) env =
 NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof) := by
 unfold model
 rw [LIBC_Bytes.from_native]
 exact (NJS_Parse.source proof).symm
theorem graph (proof : Bytes) (env : Env) (o : Obs (Except VErr Unit)) :
 child.law proof env o ↔ o = LIB_Carriers.resultObs port [] (model proof env) := Iff.rfl
#print axioms returns
#print axioms source
#print axioms graph
end LIBC_ParseShape
