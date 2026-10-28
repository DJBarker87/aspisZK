import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
set_option autoImplicit false
namespace AspisR1.JHn_ImageIdentity
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Explicit byte-level frontier: checksum equality is transported only after
identity of the actual constructed body, never from its length or header. -/
theorem source (saved : alloc.vec.Vec U8) (body : Slice U8)
    (hc : Array U8 32#usize)
    (image : saved.val=body.val ++ hc.val)
    (bodyIdentity : body.val=JFx_NativeBytes.checkpoint.val.take 1736)
    (request : AspisR1Stage2.WireTx2.checksumParts body=JFn_HashBoundary.checksumParts)
    (call : F3U_Oracle.hashv JFp_SHADigest.digest
      (AspisR1Stage2.WireTx2.checksumParts body)=ok hc)
    (checksum : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum)
    (retained : JFx_NativeBytes.checkpoint.val.drop 1736=JFo_AuthBytes.checksum.val) :
    saved.val=JFx_NativeBytes.checkpoint.val := by
  rw [request] at call
  change ok (encodeState (JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)))=ok hc at call
  rw [checksum,array_roundtrip] at call
  have same := Result.ok.inj call
  rw [image,bodyIdentity,←same,←retained,List.take_append_drop]
#print axioms source
end AspisR1.JHn_ImageIdentity
