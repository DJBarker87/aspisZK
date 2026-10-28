import NDO_JHe_WriterHeader
set_option autoImplicit false
namespace AspisR1.JHn_BodyHeader
open Aeneas Aeneas.Std
open OraclePortCkptAbi2Extracted.aspis_r1_cost_probe.verifier
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source (p : Prepared) (a : Accumulator)
    (variant : p.variant=.S2) (next : a.next.val=10) :
    (OraclePortPhysicalFrameDraft.magic.map CheckpointBytes5Writer.u8 ++
      (MultiproofConeCanonical.bytesOf [WAdm_SourceBody.tag p.variant,UScalar.cast .U8 a.next,
        1#u8,0#u8,0#u8,0#u8,0#u8,0#u8]).map CheckpointBytes5Writer.u8)=
      JFx_NativeBytes.checkpoint.val.take 16 := by
  rw [variant,CheckpointBytesHeader.next_cast a.next next,WAdm_SourceWriter.map_bytes,
    JFq_AuthBytes.first16]
  rfl
#print axioms source
end AspisR1.JHn_BodyHeader
