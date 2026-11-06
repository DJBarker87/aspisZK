import NKJ_NativeSmall
import NKJ_Small2
import NKJ_Small3
import NKJ_Small4
import NGA_WrapperValues
import NGA_Indexed
set_option autoImplicit false
namespace NKJ_Root
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Q := NGA_Cache.Q

/-- Complete bounded-domain accumulator result and adopted field value, with
native source cuts composed at the original arguments, not a free child reply. -/
theorem accumulate (s : Sums) (left right : Q)
 (hl : NGA_Cache.Canonical left) (hr : NGA_Cache.Canonical right)
 (budget : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 ∃ out, NKJ_NativeFold.accumulate s left right=ok out ∧
 NKJ_Extracted.field.NKJ_reference.NKJ_accumulate s (NKJ_Cache.words left) (NKJ_Cache.words right)=ok out ∧
 NGA_Accumulate.sourceModel s left right=ok out ∧
 NGA_Converter.interpret (NGA_Converter.decode out)=
 NGA_Converter.interpret (NGA_Converter.decode s)+NGA_ChannelAlgebra.decodeQ left*NGA_ChannelAlgebra.decodeQ right := by
 obtain ⟨l,r,out,_,_,_,_,ho,_,value⟩ := NGA_Accumulate.source s left right hl hr budget
 have ref := (NKJ_Accumulate.source s left right hl hr budget).trans ho
 exact ⟨out,(NKJ_NativeFold.accumulate_ref s left right hl hr budget).trans ref,ref,ho,value⟩

/-- The helper's exact SAME-array caller law. Its only arities are 2,3,4;
no canonicality or budget beyond the actual caller inputs is assumed. -/
theorem small {n : Usize} (left right : Array Q n)
 (_lower : 2≤n.val) (upper : n.val≤4)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 NKJ_NativeSmall.run (left.val.zip right.val)=NGA_Wrappers.small left right := by
 obtain ⟨length,domain⟩ := NGA_Wrappers.domain left right hl hr
 exact NKJ_NativeSmall.value _ (by rw [length];exact upper) domain

#print axioms accumulate
#print axioms small


theorem sum2 (left right : Array Q 2#usize)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 ∃ out, NKJ_NativeSmall.run (left.val.zip right.val)=ok out ∧
   NGA_Wrappers.sum2 left right=ok out ∧
   NKJ_Extracted.field.NKJ_reference.NKJ_small2 (NKJ_Arrays.encode left) (NKJ_Arrays.encode right)=ok (NKJ_Extracted.fromCanonical out) ∧
   NGA_Cache.Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_WrapperValues.two left right hl hr
 refine ⟨out,(small left right (by decide) (by decide) hl hr).trans ho,ho,?_,hc,hv⟩
 simp only [NKJ_Small2.source left right hl hr,ho,bind_tc_ok]
#print axioms sum2

theorem sum3 (left right : Array Q 3#usize)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 ∃ out, NKJ_NativeSmall.run (left.val.zip right.val)=ok out ∧
   NGA_Wrappers.sum3 left right=ok out ∧
   NKJ_Extracted.field.NKJ_reference.NKJ_small3 (NKJ_Arrays.encode left) (NKJ_Arrays.encode right)=ok (NKJ_Extracted.fromCanonical out) ∧
   NGA_Cache.Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_WrapperValues.three left right hl hr
 refine ⟨out,(small left right (by decide) (by decide) hl hr).trans ho,ho,?_,hc,hv⟩
 simp only [NKJ_Small3.source left right hl hr,ho,bind_tc_ok]
#print axioms sum3

theorem sum4 (left right : Array Q 4#usize)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x) :
 ∃ out, NKJ_NativeSmall.run (left.val.zip right.val)=ok out ∧
   NGA_Wrappers.sum4 left right=ok out ∧
   NKJ_Extracted.field.NKJ_reference.NKJ_small4 (NKJ_Arrays.encode left) (NKJ_Arrays.encode right)=ok (NKJ_Extracted.fromCanonical out) ∧
   NGA_Cache.Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=NGA_SumAlgebra.sumProducts (left.val.zip right.val) := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_WrapperValues.four left right hl hr
 refine ⟨out,(small left right (by decide) (by decide) hl hr).trans ho,ho,?_,hc,hv⟩
 simp only [NKJ_Small4.source left right hl hr,ho,bind_tc_ok]
#print axioms sum4
end NKJ_Root
