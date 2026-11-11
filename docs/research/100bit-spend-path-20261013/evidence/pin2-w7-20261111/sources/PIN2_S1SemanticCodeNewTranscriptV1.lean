import RPz7_S1PreparedHashCodeV1
import PIN2W7_PrefixGlue
/-! PIN2 W7 (2026-11-11): release RPz7_S1SemanticCodeNewTranscriptV1.lean re-targeted to the PIN2 emission by tools/PIN2W7_lift.py (fixed substitution table: namespace, digest trait path, PCWN_NewLib branch/map_err/from_residual, digest-event instance copy). -/
set_option autoImplicit false
namespace AspisR1PublicPreparationPIN2.S1SemanticCode
open AspisR1PublicPreparationPIN2
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode (Code)

def newTranscript
  {H : Type} (aspis_coreDigest32Inst : aspis_core.digest.Digest32 H) (hash : H)
  (public_bytes : Slice Std.U8) (c1_root : Array Std.U8 32#usize) :
  Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let i := Slice.len public_bytes
  let r ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from i
  let r1 ←
    PCWN_NewLib.core.result.Result.map_err
      (r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s ← lift (Array.to_slice (Array.make 1#usize [ 0#u8 ]))
    let a ← lift (core.num.U32.to_le_bytes val)
    let s1 ← lift (Array.to_slice a)
    let s2 ← lift (Array.to_slice c1_root)
    let s3 ←
      lift (Array.to_slice
        (Array.make 5#usize [ r1_wire.DOMAIN, s, s1, public_bytes, s2 ]))
    let a1 ← AspisR1PublicPreparation.PreparedHashCode.effects.digest
      (AspisR1PublicPreparation.PIN2W7_PrefixGlue.digestBack aspis_coreDigest32Inst) hash s3
    pure (core.result.Result.Ok { state := a1, hash, next_row := 0#u8 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms newTranscript
end AspisR1PublicPreparationPIN2.S1SemanticCode
