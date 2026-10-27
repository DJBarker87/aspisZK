import JHh_RetainedChecksum
import JHh_SHARealization
set_option autoImplicit false
namespace AspisR1.JHh_WriterBodyFrontier
open Aeneas Aeneas.Std Result
/-- Conditional image composition under only the concrete checksum field
ONCE the actual body is identified. The explicit body premise remains open. -/
theorem source [sha : JHh_SHARealization] (saved : alloc.vec.Vec U8)
    (body : Slice U8) (hc : Array U8 32#usize)
    (image : saved.val=body.val ++ hc.val)
    (bodyIdentity : body.val=JFx_NativeBytes.checkpoint.val.take 1736)
    (call : F3U_Oracle.hashv JFp_SHADigest.digest
      (AspisR1Stage2.WireTx2.checksumParts body)=ok hc) :
    saved.val=JFx_NativeBytes.checkpoint.val :=
  JHh_ImageIdentity.source saved body hc image bodyIdentity
    (JHh_RetainedChecksum.request body bodyIdentity) call
    JHh_SHARealization.checksum JHh_RetainedChecksum.suffix
#print axioms source
end AspisR1.JHh_WriterBodyFrontier
