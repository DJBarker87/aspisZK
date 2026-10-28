import NDO_JFt_ReadArray
import NDO_JFu_PublicBindings
import NDO_JFu_PublicIndices
set_option autoImplicit false
namespace AspisR1.JFt_Metadata
open Aeneas Aeneas.Std Result

theorem pool : AspisS6NativeSnapshotReadArray.read_array 32#usize
    (JFu_PublicRange.segment 224 32 (by decide))=ok JFu_PublicBindings.pool :=
  JFt_ReadArray.source _ _ _ _ _ JFu_PublicBindings.pool_selected

theorem domain : AspisS6NativeSnapshotReadArray.read_array 32#usize
    (JFu_PublicRange.segment 256 32 (by decide))=ok JFu_PublicBindings.domain :=
  JFt_ReadArray.source _ _ _ _ _ JFu_PublicBindings.domain_selected

theorem sequence : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (JFu_PublicRange.segment 288 8 (by decide))=ok JFu_PublicIndices.before :=
  JFt_ReadArray.source _ _ _ _ _ JFu_PublicIndices.sequence_bytes

theorem index : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (JFu_PublicRange.segment 296 8 (by decide))=ok JFu_PublicIndices.before :=
  JFt_ReadArray.source _ _ _ _ _ JFu_PublicIndices.index_bytes

theorem next : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (JFu_PublicRange.segment 984 8 (by decide))=ok JFu_PublicIndices.after :=
  JFt_ReadArray.source _ _ _ _ _ JFu_PublicIndices.next_bytes

#print axioms pool
#print axioms domain
#print axioms sequence
#print axioms index
#print axioms next
end AspisR1.JFt_Metadata
