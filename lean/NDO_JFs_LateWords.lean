import NDO_JFs_LateBytes
import NDO_JFt_ReadArray
set_option autoImplicit false
namespace AspisR1.JFs_LateWords
open Aeneas Aeneas.Std Result

def a10 : Array U8 2#usize := ⟨(JFu_PublicMeta00.bytes.drop 10).take 2,by simp [JFu_PublicMeta00.bytes]⟩
theorem selected10 : (JFu_PublicRange.segment 154 2 (by decide)).val=a10.val :=
  JFt_LocalWindow.selected 144 32 10 2 (by decide) (by decide) _ JFu_PublicMeta00.selected
theorem read10 : AspisS6NativeSnapshotReadArray.read_array 2#usize
    (JFu_PublicRange.segment 154 2 (by decide))=ok a10 :=
  JFt_ReadArray.source _ _ _ _ _ selected10
theorem word10 : core.num.U16.from_le_bytes a10=32#u16 := by rfl
theorem cast10 : UScalar.cast .Usize 32#u16=32#usize := by scalar_tac

def a12 : Array U8 4#usize := ⟨(JFu_PublicMeta00.bytes.drop 12).take 4,by simp [JFu_PublicMeta00.bytes]⟩
theorem selected12 : (JFu_PublicRange.segment 156 4 (by decide)).val=a12.val :=
  JFt_LocalWindow.selected 144 32 12 4 (by decide) (by decide) _ JFu_PublicMeta00.selected
theorem read12 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (JFu_PublicRange.segment 156 4 (by decide))=ok a12 :=
  JFt_ReadArray.source _ _ _ _ _ selected12
theorem word12 : core.num.U32.from_le_bytes a12=800#u32 := by rfl
theorem cast12 : UScalar.cast .Usize 800#u32=800#usize := by scalar_tac

def a16 : Array U8 4#usize := ⟨(JFu_PublicMeta00.bytes.drop 16).take 4,by simp [JFu_PublicMeta00.bytes]⟩
theorem selected16 : (JFu_PublicRange.segment 160 4 (by decide)).val=a16.val :=
  JFt_LocalWindow.selected 144 32 16 4 (by decide) (by decide) _ JFu_PublicMeta00.selected
theorem read16 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (JFu_PublicRange.segment 160 4 (by decide))=ok a16 :=
  JFt_ReadArray.source _ _ _ _ _ selected16
theorem word16 : core.num.U32.from_le_bytes a16=688#u32 := by rfl
theorem cast16 : UScalar.cast .Usize 688#u32=688#usize := by scalar_tac

def a20 : Array U8 4#usize := ⟨(JFu_PublicMeta00.bytes.drop 20).take 4,by simp [JFu_PublicMeta00.bytes]⟩
theorem selected20 : (JFu_PublicRange.segment 164 4 (by decide)).val=a20.val :=
  JFt_LocalWindow.selected 144 32 20 4 (by decide) (by decide) _ JFu_PublicMeta00.selected
theorem read20 : AspisS6NativeSnapshotReadArray.read_array 4#usize
    (JFu_PublicRange.segment 164 4 (by decide))=ok a20 :=
  JFt_ReadArray.source _ _ _ _ _ selected20
theorem word20 : core.num.U32.from_le_bytes a20=1520#u32 := by rfl
theorem cast20 : UScalar.cast .Usize 1520#u32=1520#usize := by scalar_tac

#print axioms selected10
#print axioms read10
#print axioms word10
#print axioms cast10
#print axioms selected12
#print axioms read12
#print axioms word12
#print axioms cast12
#print axioms selected16
#print axioms read16
#print axioms word16
#print axioms cast16
#print axioms selected20
#print axioms read20
#print axioms word20
#print axioms cast20
end AspisR1.JFs_LateWords
