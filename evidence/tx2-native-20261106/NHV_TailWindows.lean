import NHV_WindowFrame
import NHT_Offsets
set_option autoImplicit false
namespace NHV_TailWindows
open Aeneas Aeneas.Std Result
/-- Exact value of any successful native slice port; no buffer-byte assumption. -/
theorem range_value (proof out : Slice U8) (lo hi : Usize)
 (bounds : lo≤hi ∧ hi.val≤proof.length)
 (returned : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proof {start:=lo,«end»:=hi}=ok out) :
 out.val=List.slice lo.val hi.val proof.val := by
 simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
   core.slice.index.SliceIndexRangeUsizeSlice.index,if_pos bounds] at returned
 cases returned
 rfl

/-- All four byte widths at TX2's actual source boundaries follow from the
original proof length. This does not assert any field decoder accepts. -/
theorem widths (proof : Slice U8) (bound : 10055≤proof.val.length) :
 ((proof.val.drop 7495).take 32).length=32 ∧
 ((proof.val.drop 7527).take 224).length=224 ∧
 ((proof.val.drop 7751).take 32).length=32 ∧
 ((proof.val.drop 7783).take 224).length=224 ∧
 ((proof.val.drop 8007).take 2048).length=2048 := by
 exact ⟨NHV_WindowFrame.width _ _ _ (by omega),
  NHV_WindowFrame.width _ _ _ (by omega),
  NHV_WindowFrame.width _ _ _ (by omega),
  NHV_WindowFrame.width _ _ _ (by omega),
  NHV_WindowFrame.width _ _ _ (by omega)⟩

/-- Same proof and ordered source windows: concatenation has no invented gap. -/
theorem stored_tail (proof : List U8) :
 (proof.drop 7527).take 224 ++ (proof.drop 7751).take 32 ++
   (proof.drop 7783).take 224 ++ (proof.drop 8007).take 2048 =
 (proof.drop 7527).take 2528 := by
 rw [NHV_WindowFrame.adjacent proof 7527 224 32]
 rw [NHV_WindowFrame.adjacent proof 7527 256 224]
 exact NHV_WindowFrame.adjacent proof 7527 480 2048
#print axioms range_value
#print axioms widths
#print axioms stored_tail
end NHV_TailWindows
