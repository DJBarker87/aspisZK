import NDO_JGz_ChecksumSHA
import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
set_option autoImplicit false
namespace AspisR1.JGz_ChecksumDigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
theorem native : (flatten JFn_HashBoundary.checksumParts).map Fin.val=JGz_ChecksumSHA.raw := by
  simp only [flatten,JFn_HashBoundary.checksumParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map,Function.comp_def,decodeByte,id_eq,JFq_Range.segment,JFx_NativeBytes.checkpoint,JFx_NativeBytes.checkpointBytes,List.drop_zero]
  change (JGz_ChecksumNative.domain ++ JFx_DataCheckpoint00.bytes.take 1736).map (fun x=>x.val)=_
  rw [JGz_ChecksumNative.native]
  simp only [JGz_ChecksumSHA.raw,JGz_ChecksumSHA.head,JGz_ChecksumNative.raw,JGz_ChecksumNative.chunks,JGz_SHAC00.chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms native
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum := by
  unfold JFp_SHADigest.digest
  rw [native,JGz_ChecksumSHA.checked]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.JGz_ChecksumDigest
