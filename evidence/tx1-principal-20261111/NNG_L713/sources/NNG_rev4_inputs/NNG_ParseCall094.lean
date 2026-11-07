import NNG_Context094
import LIBC_ParseShape
import NMP_ResultTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParseCall094
open Aeneas Aeneas.Std Result NMT_tx1

def errorBack : LIB_VCarriers.VErr → verifier.Error
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation
def error : verifier.Error → LIB_VCarriers.VErr
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def variant : Op3I_Source.transport.Variant → transport.Variant
 | .S1=>.S1 | .S2=>.S2 | .D=>.D
def reply : core.result.Result Op3I_Source.transport.Variant Op3I_Source.verifier.Error →
 core.result.Result transport.Variant verifier.Error
 | .Ok v=>.Ok (variant v) | .Err e=>.Err (errorBack (LIBC_ParseShape.error e))
def port : core.result.Result transport.Variant verifier.Error → Except LIB_VCarriers.VErr Unit
 | .Ok _=>.ok () | .Err e=>.error (error e)
def call (env : RSL.Env) (proof : Slice U8) :=
 NMP_ResultTransport.outer reply (LIBC_ParseShape.model (LIB_Carriers.bytes proof) env)

theorem error_inverse (e : LIB_VCarriers.VErr) : error (errorBack e)=e := by cases e <;> rfl
#print axioms error_inverse

theorem reply_port (r : core.result.Result Op3I_Source.transport.Variant Op3I_Source.verifier.Error) :
 port (reply r)=LIBC_ParseShape.port r := by
 cases r with
 | Ok v=>rfl
 | Err e=>exact congrArg Except.error (error_inverse _)
#print axioms reply_port

/-- All source arms, including length rejection, are covered by the actual
CLOSED086 source association. No proof-width input premise is needed. -/
theorem source (env : RSL.Env) (proof : Slice U8) :
 call env proof=NMP_ResultTransport.outer reply
 (NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof)) := by
 unfold call
 rw [LIBC_ParseShape.source]
#print axioms source

theorem graph (env : RSL.Env) (proof : Slice U8) :
 LIBC_ParseShape.child.law (LIB_Carriers.bytes proof) env
  (LIB_Carriers.resultObs port [] (call env proof)) := by
 apply (LIBC_ParseShape.graph _ env _).mpr
 unfold call
 generalize LIBC_ParseShape.model (LIB_Carriers.bytes proof) env=r
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok r=>
   exact congrArg (fun value=>RSL.Obs.mk (RSL.Exit.ret value) []) (reply_port r)
#print axioms graph
end AspisR1.NNG_ParseCall094
