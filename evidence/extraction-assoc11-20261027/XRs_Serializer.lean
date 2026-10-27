import XRs_WordBytes
import S1OriginalSerializerInstallationV1
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_Serializer
open AspisR1CurrentCaller.OriginalSerializerInstallation

theorem same_eight_limbs (x : XRn_Join_Wide) :
 aspis_core.field.wide_exact.WideExact.to_le_bytes x = sourceBytes x := by
 rw [sourceBytes_total]
 unfold aspis_core.field.wide_exact.WideExact.to_le_bytes
 unfold XRn_Join_qBytes XRn_Join_FieldExternal.newQ
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,XRs_WordBytes.word]
 have h : (AspisR1WideToBytesIndexedCandidate.expectedList
   (P6ToBytes.IndexedCarrierBridge.toIndexed (sourceCarrier x))).length = 32 := by
  simp only [AspisR1WideToBytesIndexedCandidate.expectedList,List.length_append,
   AspisR1WideToBytesIndexedCandidate.limbBytes_length]
 rw [dif_pos (by exact h)]
 congr 1
#print axioms same_eight_limbs
end XRs_Serializer
