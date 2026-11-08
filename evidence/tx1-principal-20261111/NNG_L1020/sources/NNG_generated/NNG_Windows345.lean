import NNG_Tree345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Windows345
open Aeneas Aeneas.Std Result

def window (s : Slice U8) (lo hi : Nat) : Slice U8 :=
 ⟨(s.val.drop lo).take (hi-lo),by
  have hs : s.val.length ≤ Usize.max := s.property
  change ((s.val.drop lo).take (hi-lo)).length ≤ Usize.max
  rw [List.length_take,List.length_drop]
  omega⟩

theorem range (s : Slice U8) (lo hi : Usize) (bounds : lo≤hi ∧ hi.val≤s.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s {start:=lo,«end»:=hi}=ok (window s lo.val hi.val) := by
 change (if lo≤hi ∧ hi.val≤s.length then _ else _)=_
 rw [if_pos bounds]
 apply congrArg Result.ok
 apply Subtype.ext
 rfl
#print axioms range

theorem prefix_range (s : Slice U8) (hi : Usize) (bounds : hi.val≤s.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
  s {«end»:=hi}=ok (window s 0 hi.val) := by
 change (if hi.val≤s.length then _ else _)=_
 rw [if_pos bounds]
 apply congrArg Result.ok
 apply Subtype.ext
 rfl
#print axioms prefix_range

theorem index (s : Slice U8) (i : Usize) (h : i.val < s.val.length) :
 Slice.index_usize s i=ok (s.val[i.val]'h) := by
 obtain ⟨x,returned,value⟩ := WP.spec_imp_exists (Slice.index_usize_spec s i h)
 exact returned.trans (congrArg Result.ok value)
#print axioms index

theorem bytes (s : Slice U8) (lo hi : Nat) :
 LIB_Carriers.bytes (window s lo hi)=RSL.slice (LIB_Carriers.bytes s) lo hi := by
 unfold window RSL.slice LIB_Carriers.bytes NMS_R2N_RSLScalars.bytes
 simp only [List.map_take,List.map_drop]
#print axioms bytes
end AspisR1.NNG_Windows345
