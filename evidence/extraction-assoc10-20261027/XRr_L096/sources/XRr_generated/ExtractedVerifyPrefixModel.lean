import ExtractedPrefixParseCore
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
abbrev VerifyPrefix.Finish := {H : Type} → aspis_core.Digest32 H →
  pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
def VerifyPrefix.mark
  (obs : Option (verifier.Phase → Result Unit)) (i : Std.U8) :
  Result Unit
  := do
  ok ()

def VerifyPrefix.verify (F : VerifyPrefix.Finish)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ← PrefixAdapter.parseAccepted bytes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    VerifyPrefix.mark obs 0#u8
    let r1 ←
      r1_semantic.public_transcript aspis_coreDigest32Inst public1 hash
        p.c1_root
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, val1) ← r1_wire.begin aspis_coreDigest32Inst p val
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        VerifyPrefix.mark obs 1#u8
        F aspis_coreDigest32Inst public1 p val1 val2
          obs
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

#print axioms VerifyPrefix.mark
#print axioms VerifyPrefix.verify
end AspisR1PublicPreparation
