import S1SemanticCodeSampleBlockV1
import S1SemanticFinishModelV1
import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def newTranscript
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) (hash : H)
  (public_bytes : Slice Std.U8) (c1_root : Array Std.U8 32#usize) :
  Code (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
  := do
  let i := Slice.len public_bytes
  let r ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from i
  let r1 ←
    core.result.Result.map_err
      (r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s ← lift (Array.to_slice (Array.make 1#usize [ 0#u8 ]))
    let a ← lift (core.num.U32.to_le_bytes val)
    let s1 ← lift (Array.to_slice a)
    let s2 ← lift (Array.to_slice c1_root)
    let s3 ←
      lift (Array.to_slice
        (Array.make 5#usize [ r1_wire.DOMAIN, s, s1, public_bytes, s2 ]))
    let a1 ← PreparedHashCode.effects.digest aspis_coreDigest32Inst hash s3
    pure (core.result.Result.Ok { state := a1, hash, next_row := 0#u8 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error)
      residual

#print axioms newTranscript
end AspisR1PublicPreparation.S1SemanticCode
