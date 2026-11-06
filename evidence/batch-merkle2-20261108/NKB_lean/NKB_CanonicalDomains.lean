import NKB_CanonicalPrefix
set_option autoImplicit false
namespace NKB_CanonicalDomains
open Aeneas Aeneas.Std Result AspisR1

theorem c1 (q : Slice U8) (length : q.val.length=832) (s : Usize) (slot : s.val<4) :
 (NKB_CanonicalTail.window q s).val.length=16 := by
 have a:=NKB_CanonicalTail.address s slot
 rw [NKB_CanonicalTail.window,MultiproofConeSlices.sub_length q
   (NKB_CanonicalTail.start s) (NKB_CanonicalTail.finish s) (by omega) (by omega)]
 omega

theorem c2 (q : Slice U8) (length : q.val.length=832) (s l : Usize)
 (slot : s.val<4) (lane : l.val<2) :
 (NKB_CanonicalRange.window q s l).val.length=16 := by
 have a:=NKB_CanonicalRange.address s l slot lane
 rw [NKB_CanonicalRange.window,MultiproofConeSlices.sub_length q
   (NKB_CanonicalRange.start s l) (NKB_CanonicalRange.finish s l) (by omega) (by omega)]
 omega

theorem trailing (q : Slice U8) (length : q.val.length=832) :
 (NKB_CanonicalOpening.trailing q).val.length=128 := by
 rw [NKB_CanonicalOpening.trailing,MultiproofConeSlices.sub_length q 672#usize 800#usize (by decide) (by change 800≤q.val.length;omega)]
 rfl

theorem prefix_windows (proof : Slice U8) (length : proof.val.length=57607) :
 (NKB_CanonicalPrefix.values proof).val.length=464 ∧
 (NKB_CanonicalPrefix.inactive proof).val.length=32 ∧
 (NKB_CanonicalPrefix.round0 proof).val.length=224 ∧
 (NKB_CanonicalPrefix.round1 proof).val.length=2272 := by
 simp only [NKB_CanonicalPrefix.values,NKB_CanonicalPrefix.inactive,
   NKB_CanonicalPrefix.round0,NKB_CanonicalPrefix.round1]
 rw [MultiproofConeSlices.sub_length proof 7031#usize 7495#usize (by decide) (by change 7495≤proof.val.length;omega),
   MultiproofConeSlices.sub_length proof 7495#usize 7527#usize (by decide) (by change 7527≤proof.val.length;omega),
   MultiproofConeSlices.sub_length proof 7527#usize 7751#usize (by decide) (by change 7751≤proof.val.length;omega),
   MultiproofConeSlices.sub_length proof 7783#usize 10055#usize (by decide) (by change 10055≤proof.val.length;omega)]
 exact ⟨rfl,rfl,rfl,rfl⟩

/-- Every echeck call is in the CLOSED NJZ domain, which is all slices and
both flags. No stronger ten/twelve-query or field-canonicality premise appears. -/
theorem aligned (proof q : Slice U8) (pl : proof.val.length=57607) (ql : q.val.length=832) :
 (NKB_CanonicalPrefix.inactive proof).val.length%32=0 ∧
 (NKB_CanonicalPrefix.round0 proof).val.length%32=0 ∧
 (NKB_CanonicalPrefix.round1 proof).val.length%32=0 ∧
 (NKB_CanonicalOpening.trailing q).val.length%32=0 := by
 obtain ⟨_,a,b,c⟩:=prefix_windows proof pl
 rw [a,b,c,trailing q ql]
 decide

#print axioms c1
#print axioms c2
#print axioms trailing
#print axioms prefix_windows
#print axioms aligned
end NKB_CanonicalDomains
