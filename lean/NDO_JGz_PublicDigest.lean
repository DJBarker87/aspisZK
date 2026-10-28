import NDO_JGz_PublicSHA
import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
set_option autoImplicit false
namespace AspisR1.JGz_PublicDigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
theorem native : (flatten JFn_HashBoundary.publicParts).map Fin.val=JGz_PublicSHA.raw := by
  simp only [flatten,JFn_HashBoundary.publicParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map,Function.comp_def,decodeByte,id_eq,JFx_NativeBytes.publicInput,JFx_NativeBytes.publicBytes]
  rw [JGz_PublicNative.native]
  simp only [JGz_PublicSHA.raw,JGz_PublicSHA.head,JGz_PublicNative.chunks,JGz_SHAU00.chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms native
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=decodeState JFo_AuthBytes.publicHash := by
  unfold JFp_SHADigest.digest
  rw [native,JGz_PublicSHA.checked]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.JGz_PublicDigest
