import NDO_JGz_ProofSHA
import NDO_JFn_HashBoundary
import NDO_JFp_SHADigest
import NDO_JGz_ProofNative00
import NDO_JGz_ProofNative01
import NDO_JGz_ProofNative02
import NDO_JGz_ProofNative03
import NDO_JGz_ProofNative04
import NDO_JGz_ProofNative05
import NDO_JGz_ProofNative06
import NDO_JGz_ProofNative07
import NDO_JGz_ProofNative08
import NDO_JGz_ProofNative09
import NDO_JGz_ProofNative10
import NDO_JGz_ProofNative11
import NDO_JGz_ProofNative12
import NDO_JGz_ProofNative13
set_option autoImplicit false
namespace AspisR1.JHi_SHAProof
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
theorem native : (flatten JFn_HashBoundary.proofParts).map Fin.val=JGz_ProofSHA.raw := by
  simp only [flatten,JFn_HashBoundary.proofParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map,Function.comp_def,decodeByte,id_eq,JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes]
  rw [JGz_ProofNative00.native,JGz_ProofNative01.native,JGz_ProofNative02.native,JGz_ProofNative03.native,JGz_ProofNative04.native,JGz_ProofNative05.native,JGz_ProofNative06.native,JGz_ProofNative07.native,JGz_ProofNative08.native,JGz_ProofNative09.native,JGz_ProofNative10.native,JGz_ProofNative11.native,JGz_ProofNative12.native,JGz_ProofNative13.native,JGz_ProofNative14.native]
  simp only [JGz_ProofSHA.raw,JGz_ProofSHA.head,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms native
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash := by
  unfold JFp_SHADigest.digest
  rw [native,JGz_ProofSHA.checked]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.JHi_SHAProof
