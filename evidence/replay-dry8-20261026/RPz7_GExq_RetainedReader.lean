import RPz7_GExp_FirstAccepted
import Port8EFF_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_RetainedReader
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect

def code (reserved : Bool)
    (ck proof pub : Slice U8) (v : transport.Variant) :
    Code (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let out ← Port8EFF_NativeReader.program (CheckpointBytes4Ops.ops reserved) ck proof pub v
  pure (match out with
    | .Ok pair => .Ok pair
    | .Err e => .Err (Port3_CheckpointInstall.error e))

theorem source {Hash : Type} (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (law : ∀ parts, D.digest hash parts = hashv parts)
    (ck proof pub : Slice U8) (v : transport.Variant) :
    erase (SdkC_Source.dictionary hashv) () (code reserved ck proof pub v) =
      Port4A_ReaderInstall.reader reserved D ck proof pub v hash := by
  rw [← SdkC_Source.erasure hashv _ [],SdkC_Source.erasure_to (VTop_Checkpoint.digest D) hash hashv law]
  simp only [code,erase_bind,erase_pure,Port8EFF_NativeReader.source]
  unfold Port4A_ReaderInstall.reader
  congr 1
  funext out
  cases out <;> rfl

#print axioms source
end AspisR1.GExq_RetainedReader
end
