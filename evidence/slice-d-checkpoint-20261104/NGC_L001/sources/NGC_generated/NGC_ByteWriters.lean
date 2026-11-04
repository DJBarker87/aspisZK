import NFT_QByteFrame
set_option autoImplicit false
namespace NGC_ByteWriters
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted
/-- Checkpoint CM writer uses the SAME input and output slice; no canonicality premise. -/
theorem cm (q : aspis_core.field.CM31) (out : Slice U8) (length : 8≤out.val.length) :
 ∃ final, aspis_core.field.CM31.write_le_bytes q out=ok final ∧
 final.val=NFT_Bytes.cmBytes q ++ out.val.drop 8 := NFT_Bytes.cm_frame q out length
/-- Checkpoint QM writer uses the SAME input and output slice; suffix preserved. -/
theorem qm (q : aspis_core.field.QM31) (out : Slice U8) (length : 16≤out.val.length) :
 ∃ final, aspis_core.field.QM31.write_le_bytes q out=ok final ∧
 final.val=NFT_Bytes.qmBytes q ++ out.val.drop 16 := NFT_Bytes.qm_frame q out length
#print axioms cm
#print axioms qm
end NGC_ByteWriters
