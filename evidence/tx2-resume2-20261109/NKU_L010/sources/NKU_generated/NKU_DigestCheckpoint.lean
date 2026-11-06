import NKU_Chronology
import NKK_DigestSource
set_option autoImplicit false
noncomputable section
namespace NKU_DigestCheckpoint
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def label : Array U8 22#usize := Array.make 22#usize [
 85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,
 58#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]
/-- Native checkpoint digest G: literal22, SAME bytes[0..end], SAME stored
suffix. NKK_K036/K043/K044 have domain end=1736/backing1768. -/
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 («end» : Usize) : Stage Unit := fun s => do
 let stored ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) s.frame.checkpoint { start := «end» }
 let tag ← lift (Array.to_slice label)
 let cpView ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s.frame.checkpoint { «end» := «end» }
 let chunks ← lift (Array.to_slice (Array.make 2#usize [tag,cpView]))
 NKK_DigestSource.model d hash chunks stored (pure (.Ok ((),{s with phase := .roots})))
def source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 («end» : Usize) : Stage Unit := fun s => do
 let stored ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) s.frame.checkpoint { start := «end» }
 let tag ← lift (Array.to_slice label)
 let cpView ← core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s.frame.checkpoint { «end» := «end» }
 let chunks ← lift (Array.to_slice (Array.make 2#usize [tag,cpView]))
 NKK_DigestSource.source d hash chunks stored (pure (.Ok ((),{s with phase := .roots})))
theorem source_eq_run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) («end» : Usize) (s : NKU.State) : source d hash «end» s=run d hash «end» s := by
 unfold source run
 apply NKK_LogAlgebra.bind_congr
 intro stored
 apply NKK_LogAlgebra.bind_congr
 intro tag
 apply NKK_LogAlgebra.bind_congr
 intro cpView
 apply NKK_LogAlgebra.bind_congr
 intro chunks
 exact NKK_DigestSource.source_eq_model d hash _ _ _
#print axioms source_eq_run
end NKU_DigestCheckpoint
