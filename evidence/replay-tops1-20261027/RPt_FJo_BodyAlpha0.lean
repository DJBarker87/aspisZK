import RPt_FJo_BodySlice
import CheckpointBytesSparseE
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_BodyAlpha0
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec
/-- The actual sparse body selects the exact first-alpha encoding. -/
theorem value (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (hp hu : Array U8 32#usize)
    (canonical : CanonicalWide (p.alpha.val[0]'(by simp [p.alpha.property]))) :
    slice (CheckpointBytesDecodeC5.sourceBody p a hp hu) 240 32=
      OraclePortCheckpointAbiC5.encodeE (exactE (p.alpha.val[0]'(by simp [p.alpha.property])) canonical) := by
  apply FJo_BodySlice.value p a hp hu 240 (by decide) _ (FoldedLeafCodec.encodeWide_length _)
  intro i
  exact CheckpointBytesSparseE.alpha0_c5 p a hp hu canonical
    (Usize.ofNat i.val (by have:=i.isLt;scalar_tac)) i.isLt
#print axioms value
end AspisR1.FJo_BodyAlpha0
end
