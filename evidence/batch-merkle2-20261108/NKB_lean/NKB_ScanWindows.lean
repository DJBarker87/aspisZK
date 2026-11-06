import MultiproofConeOpeningAdapters
import MultiproofConeOpeningScan

set_option autoImplicit false
namespace NKB_ScanWindows
open Aeneas Aeneas.Std Result AspisR1

/-- Every reached scalar and extension-field read in canonical_scan is inside
its SAME 832-byte opening. No echeck success or field canonicality is assumed. -/
theorem offsets (s l : Nat) (slot : s<4) (scalar : l<26) :
 s*120+l*4+4≤480 ∧ s*120+104+16≤480 ∧
 480+s*32+2*16≤608 ∧ 672+128≤832 := by omega

theorem subdomain (q : Slice U8) (length : q.val.length=832)
    (start finish : Usize) (order : start.val≤finish.val) (ending : finish.val≤832) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   q {start:=start,«end»:=finish} = ok (MultiproofConeSlices.sub q start finish) ∧
 (MultiproofConeSlices.sub q start finish).val.length=finish.val-start.val := by
 exact ⟨MultiproofConeSlices.range_total q start finish order (by omega),
   MultiproofConeSlices.sub_length q start finish order (by omega)⟩

#print axioms offsets
#print axioms subdomain
end NKB_ScanWindows
