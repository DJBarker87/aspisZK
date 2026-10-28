import RPz7_WAdm_SourceWriter
set_option autoImplicit false
namespace AspisR1.JHn_ImageBytes
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
/-- Invert the actual source conversion; no caller-chosen output bytes. -/
theorem source (bytes : Bytes) (body : Slice U8)
    (call : WAdm_SourceWriter.toSlice bytes=ok body) :
    body.val=bytes.map CheckpointBytes5Writer.u8 := by
  unfold WAdm_SourceWriter.toSlice at call
  split at call
  next h => exact (congrArg Subtype.val (Result.ok.inj call)).symm
  next h => cases call
#print axioms source
end AspisR1.JHn_ImageBytes
