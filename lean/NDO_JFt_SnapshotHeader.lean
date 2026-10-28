import NDO_JFt_LocalWindow
import NDO_JFu_PublicMeta01
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def magic : Slice U8 := ⟨JFu_PublicMeta01.bytes.take 8,by simp [JFu_PublicMeta01.bytes];scalar_tac⟩
def format : Slice U8 := ⟨(JFu_PublicMeta01.bytes.drop 16).take 32,by simp [JFu_PublicMeta01.bytes];scalar_tac⟩

theorem magic_selected : JFu_PublicRange.segment 176 8 (by decide)=magic := by
  apply Subtype.ext
  exact JFt_LocalWindow.selected 176 48 0 8 (by decide) (by decide) _ JFu_PublicMeta01.selected

theorem format_selected : JFu_PublicRange.segment 192 32 (by decide)=format := by
  apply Subtype.ext
  exact JFt_LocalWindow.selected 176 48 16 32 (by decide) (by decide) _ JFu_PublicMeta01.selected

#print pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
#print axioms magic_selected
#print axioms format_selected
end AspisR1.JFt_SnapshotHeader
