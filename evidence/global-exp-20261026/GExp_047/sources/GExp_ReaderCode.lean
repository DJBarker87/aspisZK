import GExp_FirstAccepted
import Port8EFF_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_ReaderCode
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect

def code (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (ck proof pub : Slice U8) (v : transport.Variant) :
    Code (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← Port8EFF_NativeReader.program (Port6CK_Ops.ops reserved unwrap) ck proof pub v
  pure (match out with
    | .Ok pair => .Ok pair
    | .Err e => .Err (Port3_CheckpointInstall.error e))

theorem source (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (law : ∀ parts, D.digest () parts = hashv parts)
    (ck proof pub : Slice U8) (v : transport.Variant) :
    erase (SdkC_Source.dictionary hashv) () (code reserved unwrap ck proof pub v) =
      Port6CK_Reader.reader reserved unwrap D ck proof pub v () := by
  rw [← SdkC_Source.erasure hashv _ [],SdkC_Source.erasure_to (VTop_Checkpoint.digest D) () hashv law]
  simp only [code,erase_bind,erase_pure,Port8EFF_NativeReader.source]
  unfold Port6CK_Reader.reader
  congr 1
  funext out
  cases out <;> rfl

#print axioms source
end AspisR1.GExp_ReaderCode
end
