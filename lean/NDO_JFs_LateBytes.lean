import NDO_JFs_IndexWindow
import NDO_JFu_PublicMeta00
set_option autoImplicit false
namespace AspisR1.JFs_LateBytes
open Aeneas Aeneas.Std Result

def magic : Slice U8 := ⟨JFu_PublicMeta00.bytes.take 8,by simp [JFu_PublicMeta00.bytes];scalar_tac⟩
theorem magic_selected : JFu_PublicRange.segment 144 8 (by decide)=magic := by
  apply Subtype.ext
  exact JFt_LocalWindow.selected 144 32 0 8 (by decide) (by decide) _ JFu_PublicMeta00.selected

theorem b8 : Slice.index_usize JFu_PublicRange.late 8#usize=ok 1#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 8#usize (by decide) (by decide)
    1#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b9 : Slice.index_usize JFu_PublicRange.late 9#usize=ok 2#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 9#usize (by decide) (by decide)
    2#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b24 : Slice.index_usize JFu_PublicRange.late 24#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 24#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b25 : Slice.index_usize JFu_PublicRange.late 25#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 25#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b26 : Slice.index_usize JFu_PublicRange.late 26#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 26#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b27 : Slice.index_usize JFu_PublicRange.late 27#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 27#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b28 : Slice.index_usize JFu_PublicRange.late 28#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 28#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b29 : Slice.index_usize JFu_PublicRange.late 29#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 29#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b30 : Slice.index_usize JFu_PublicRange.late 30#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 30#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

theorem b31 : Slice.index_usize JFu_PublicRange.late 31#usize=ok 0#u8 := by
  exact JFs_IndexWindow.source 144 1520 32 (by decide) 31#usize (by decide) (by decide)
    0#u8 JFu_PublicMeta00.bytes JFu_PublicMeta00.selected (by rfl)

#print axioms magic_selected
#print axioms b8
#print axioms b9
#print axioms b24
#print axioms b25
#print axioms b26
#print axioms b27
#print axioms b28
#print axioms b29
#print axioms b30
#print axioms b31
end AspisR1.JFs_LateBytes
