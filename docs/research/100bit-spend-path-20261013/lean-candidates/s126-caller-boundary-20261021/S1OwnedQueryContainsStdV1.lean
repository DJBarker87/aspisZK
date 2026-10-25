import S1OwnedQueryContainsMeaningV1
import Query31ExplicitScanConcreteSteps
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result

theorem memberFrom_prefix (a : Array U32 22#usize) (len : Usize) (candidate : U32)
    (hlen : len.val≤22) :
    MemberFrom a len.val 0 candidate ↔ candidate∈a.val.take len.val := by
  have alen : a.val.length=22 := a.property
  constructor
  · rintro ⟨k,_,hk,value⟩
    have kb : k<a.val.length := by omega
    have kt : k<(a.val.take len.val).length := by simp only [List.length_take];omega
    have equal : a.val[k]'kb=candidate := by
      simpa only [List.getElem?_eq_getElem kb,Option.some.injEq] using value
    exact List.mem_iff_getElem.mpr ⟨k,kt,by simpa only [List.getElem_take] using equal⟩
  · intro member
    obtain ⟨k,hk,equal⟩ := List.mem_iff_getElem.mp member
    have kb : k<a.val.length := by simp only [List.length_take] at hk;omega
    refine ⟨k,Nat.zero_le _,by simp only [List.length_take] at hk;omega,?_⟩
    simp only [List.getElem?_eq_getElem kb,Option.some.injEq]
    simpa only [List.getElem_take] using equal

/-- Complete owned membership Result equals the concrete list-based Std model.
All child success/range premises have been derived on the admitted prefix. -/
theorem contains_eq_mem (a : Array U32 22#usize) (len : Usize) (candidate : U32)
    (hlen : len.val≤22) :
    owned_contains a len candidate=ok (decide (candidate∈a.val.take len.val)) := by
  obtain ⟨out,call⟩ := Total.contains_total a len candidate hlen
  have meaning := (contains_meaning a len candidate hlen out call).trans
    (memberFrom_prefix a len candidate hlen)
  have eq : out=decide (candidate∈a.val.take len.val) := by
    cases out <;> simp_all
  rw [← eq]
  exact call

/-- Same concrete prefix bytes/words on the retained Std slice. No independent
membership or successful-owned-call hypothesis is needed. -/
theorem contains_eq_std (a : Array U32 22#usize) (len : Usize) (candidate : U32)
    (sl : Slice U32) (hlen : len.val≤22) (frame : sl.val=a.val.take len.val) :
    owned_contains a len candidate=core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate := by
  rw [contains_eq_mem a len candidate hlen,Query31ExplicitScanConcreteSteps.slice_contains_eq_mem]
  rw [frame]

#print axioms memberFrom_prefix
#print axioms contains_eq_mem
#print axioms contains_eq_std
end AspisS1OwnedQueryBlock.Meaning
