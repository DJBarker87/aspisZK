import S1SemanticCodeNewTranscriptV1
import S1SemanticFinishModelV1
import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def publicTranscript
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
  (c1_root : Array Std.U8 32#usize) :
  Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let r ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1
  let r1 ←
    core.result.Result.map_err
      (r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    newTranscript aspis_coreDigest32Inst hash s c1_root
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms publicTranscript
end AspisR1PublicPreparation.S1SemanticCode
