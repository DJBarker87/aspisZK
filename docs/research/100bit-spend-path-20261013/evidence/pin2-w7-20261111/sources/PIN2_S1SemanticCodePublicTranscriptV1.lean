import PIN2_S1SemanticCodeNewTranscriptV1
/-! PIN2 W7 (2026-11-11): release RPz7_S1SemanticCodePublicTranscriptV1.lean re-targeted to the PIN2 emission by tools/PIN2W7_lift.py (fixed substitution table: namespace, digest trait path, PCWN_NewLib branch/map_err/from_residual, digest-event instance copy). -/
set_option autoImplicit false
namespace AspisR1PublicPreparationPIN2.S1SemanticCode
open AspisR1PublicPreparationPIN2
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode (Code)

def publicTranscript
  {H : Type} (aspis_coreDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
  (c1_root : Array Std.U8 32#usize) :
  Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let r ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes public1
  let r1 ←
    PCWN_NewLib.core.result.Result.map_err
      (r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    newTranscript aspis_coreDigest32Inst hash s c1_root
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms publicTranscript
end AspisR1PublicPreparationPIN2.S1SemanticCode
