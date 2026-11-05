import NHY_EqualValue
import NHY_AllZeroBridge
import NHY_FieldRead
set_option autoImplicit false
noncomputable section
namespace NHY_NaturalReads
open Aeneas Aeneas.Std Result WP
attribute [local instance] Classical.propDecidable

def array (b : Slice U8) (off : Nat) (n : Usize) (fit : off+n.val ≤ b.val.length) : Array U8 n :=
 ⟨(b.val.drop off).take n.val,by simp only [List.length_take,List.length_drop];omega⟩

theorem read_prefix (b : Slice U8) (n : Usize) (fit : n.val ≤ b.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   b {«end»:=n}=ok (NHY_SliceRead.segment b 0 n.val) := by
 have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   b {«end»:=n} ⦃ out => out=NHY_SliceRead.segment b 0 n.val ⦄ := by
  unfold core.slice.index.Slice.index
  step*
  all_goals apply Subtype.ext
  all_goals simpa only [NHY_SliceRead.segment,List.slice,List.drop_zero,Nat.sub_zero] using out_post1
 obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
 rw [same] at call
 exact call

theorem magic (b : Slice U8) (m : Array U8 4#usize) (fit : 4 ≤ b.val.length) :
 NCX_Reference.magic b m=ok (decide (b.val.take 4=m.val)) := by
 rw [NCX_Reference.magic,read_prefix b 4#usize fit]
 simp only [lift,bind_tc_ok]
 have cap : (NHY_SliceRead.segment b 0 4).val.length ≤ 768 := by
  simp only [NHY_SliceRead.segment,List.length_take,List.length_drop];omega
 simp only [show (4#usize).val=4 from rfl]
 rw [NHY_EqualValue.value _ _ cap]
 simp only [NHY_SliceRead.segment,List.drop_zero,Array.to_slice]
 apply congrArg Result.ok
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq]

theorem zero (b : Slice U8) (cap : b.val.length ≤ 768) :
 NCX_Reference.zero b=ok (decide (b.val=List.replicate b.val.length 0#u8)) := by
 rw [NHY_ZeroRun.value b cap,propext (NHY_AllZeroBridge.view_zero b)]
 apply congrArg Result.ok
 apply Bool.eq_iff_iff.mpr
 simp only [decide_eq_true_eq]

theorem read32 (b : Slice U8) (off : Usize) (fit : off.val+32 ≤ b.val.length) :
 NCX_Reference.read32 b off=ok (array b off.val 32#usize fit) :=
 NHY_FieldRead.bytes32 b off _ fit rfl

theorem word (b : Slice U8) (off : Usize) (fit : off.val+8 ≤ b.val.length) :
 NCX_Reference.word b off=ok (core.num.U64.from_le_bytes (array b off.val 8#usize fit)) :=
 NHY_FieldRead.word64 b off _ fit rfl

#print axioms read_prefix
#print axioms magic
#print axioms zero
#print axioms read32
#print axioms word
end NHY_NaturalReads
