import RPz7_PSem_Slices
set_option autoImplicit false
namespace AspisR1.SAG_ViewBytes
open Aeneas Aeneas.Std Result

theorem region (proof selected : Slice U8) (start stop : Usize)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=start,«end»:=stop}=ok selected) :
    MultiproofConeCanonical.bytesOf selected.val =
      OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val)
        start.val (stop.val-start.val) := by
  rw [PSem_Slices.range_bytes proof selected start stop read]
  simp only [MultiproofConeCanonical.bytesOf,OraclePortCompactDraft.slice,List.map_take,List.map_drop]

theorem final (proof selected : Slice U8)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=8007#usize,«end»:=10055#usize}=ok selected) :
    MultiproofConeCanonical.bytesOf selected.val =
      OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 8007 2048 := by
  have raw := region proof selected 8007#usize 10055#usize read
  have start : (8007#usize).val = 8007 := rfl
  have stop : (10055#usize).val = 10055 := rfl
  rw [start,stop] at raw
  have width : (10055 : Nat) - 8007 = 2048 := by omega
  rw [width] at raw
  exact raw

#print axioms region
#print axioms final
end AspisR1.SAG_ViewBytes
