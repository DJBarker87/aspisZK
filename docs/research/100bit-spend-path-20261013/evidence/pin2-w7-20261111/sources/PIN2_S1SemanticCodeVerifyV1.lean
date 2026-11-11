import RPz7_S1SemanticCodeVerifyV1
import RPz7_S1PreparedHashCodeV1
import PIN2_S1SemanticCodePublicTranscriptV1
import PIN2W7_PrefixGlue
/-! PIN2 W7 (2026-11-11), coordinator option L2: the release lifted verifier
(RPz7_S1SemanticCodeVerifyV1, `S1SemanticCode.verify`) with its single changed call
replaced: `publicTranscript` (the lift of the frozen public_transcript) becomes
`publicTranscriptPIN2`, the PIN2 lift `AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript`
on the field copies (digest, toPIN2) with the result copied back.  The definition is
renamed `verifyPIN2` so that the frozen `verify` (and `Finish`) stay; the lifted
begin, finish and every log lemma over them are the release ones, unchanged. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

/-- The PIN2 lifted public transcript on the field copies, read back on the frozen carriers. -/
def publicTranscriptPIN2
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
  (c1_root : Array Std.U8 32#usize) :
  Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let x ← AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
    (PIN2W7_TranscriptCopy.digest aspis_coreDigest32Inst) (PreparationBinding.toPIN2 public1) hash c1_root
  pure (PIN2W7_PrefixGlue.cres PIN2W7_PrefixGlue.transcriptBack PIN2W7_PrefixGlue.errorBack x)

def verifyPIN2 (F : Finish)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
  Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ← PrefixAdapter.parseAccepted bytes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    VerifyPrefix.mark obs 0#u8
    let r1 ←
      publicTranscriptPIN2 aspis_coreDigest32Inst public1 hash
        p.c1_root
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, val1) ← begin aspis_coreDigest32Inst p val
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

#print axioms publicTranscriptPIN2
#print axioms verifyPIN2
end AspisR1PublicPreparation.S1SemanticCode
