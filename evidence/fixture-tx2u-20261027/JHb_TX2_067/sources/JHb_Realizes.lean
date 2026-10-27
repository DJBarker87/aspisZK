import JGz_PublicDigest
import JGz_ChecksumDigest
import JHb_ProofSHA
import JFn_HashBoundary
import JFp_SHADigest
import JHb_ProofNative00
import JHb_ProofNative01
import JHb_ProofNative02
import JHb_ProofNative03
import JHb_ProofNative04
import JHb_ProofNative05
import JHb_ProofNative06
import JGz_ProofNative07
import JGz_ProofNative08
import JGz_ProofNative09
import JGz_ProofNative10
import JGz_ProofNative11
import JGz_ProofNative12
import JGz_ProofNative13
set_option autoImplicit false
namespace AspisR1.JHb_ProofDigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
theorem native : (flatten JFn_HashBoundary.proofParts).map Fin.val=JHb_ProofSHA.raw := by
  simp only [flatten,JFn_HashBoundary.proofParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map,Function.comp_def,decodeByte,id_eq,JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes]
  rw [JHb_ProofNative00.native,JHb_ProofNative01.native,JHb_ProofNative02.native,JHb_ProofNative03.native,JHb_ProofNative04.native,JHb_ProofNative05.native,JHb_ProofNative06.native,JGz_ProofNative07.native,JGz_ProofNative08.native,JGz_ProofNative09.native,JGz_ProofNative10.native,JGz_ProofNative11.native,JGz_ProofNative12.native,JGz_ProofNative13.native,JGz_ProofNative14.native]
  simp only [JHb_ProofSHA.raw,JHb_ProofSHA.head,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms native
theorem source : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash := by
  unfold JFp_SHADigest.digest
  rw [native,JHb_ProofSHA.checked]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.JHb_ProofDigest

set_option autoImplicit false
namespace AspisR1.JHb_Realizes
/-- Mathematical SHA256 on the exact same three native requests used by the
retained TX2 reader. This is not a syscall or source-to-ELF refinement. -/
theorem source : JFn_HashBoundary.Realizes JFp_SHADigest.digest :=
  ⟨JHb_ProofDigest.source,JGz_PublicDigest.source,JGz_ChecksumDigest.source⟩
#print axioms source
end AspisR1.JHb_Realizes

#print axioms AspisR1.JGz_PublicDigest.source
#print axioms AspisR1.JGz_ChecksumDigest.source
#print axioms AspisR1.JHb_ProofDigest.source
#print AspisR1.JHb_Realizes.source
