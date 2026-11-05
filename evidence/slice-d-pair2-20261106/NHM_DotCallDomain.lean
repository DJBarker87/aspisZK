import NHM_DotLoopDomain
import NHM_ArrayCanon
import NHE_FieldCanonical
set_option autoImplicit false
namespace NHM_DotCallDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev State := NHM_DotLoopDomain.State

theorem index (n : Nat) (s : State) (h : NHM_DotLoopDomain.Inv n s)
 (j : Usize) (next : NHI_RangeProgress.Range)
 (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some j,next)) :
 j.val<n ∧ s.2.count.val≤n := by
 obtain ⟨same,last,inc,more⟩ := NHI_RangeProgress.some_next s.1 next j run
 subst j
 constructor <;> omega

theorem high (p : Array NE 4#usize) (q : Array NQ 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hq : ∀ x∈q.val,canonQ x)
 (s : State) (h : NHM_DotLoopDomain.Inv 4 s) (j : Usize) (next : NHI_RangeProgress.Range)
 (iter : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some j,next))
 (x : NE) (k : NQ) (readx : Array.index_usize p j=ok x) (readq : Array.index_usize q j=ok k) :
 j.val<4 ∧ s.2.count.val<4096 ∧ canonE x ∧ canonQ k := by
 obtain ⟨small,count⟩ := index 4 s h j next iter
 exact ⟨small,by omega,NHM_ArrayCanon.read canonE p j x hp readx,
  NHM_ArrayCanon.read canonQ q j k hq readq⟩

theorem partial (f : Slice U8) (q : Array NQ 16#usize) (hq : ∀ x∈q.val,canonQ x)
 (offset : Usize) (side : offset.val<4) (s : State) (h : NHM_DotLoopDomain.Inv 16 s)
 (j : Usize) (next : NHI_RangeProgress.Range)
 (iter : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some j,next))
 (x : NE) (k : NQ) (readx : FIo_Native.weights.field f (NHI_PartialIndex.index offset j)=ok x)
 (readq : Array.index_usize q j=ok k) :
 (NHI_PartialIndex.index offset j).val=16*offset.val+j.val ∧
 (NHI_PartialIndex.index offset j).val<64 ∧ s.2.count.val<4096 ∧ canonE x ∧ canonQ k := by
 obtain ⟨small,count⟩ := index 16 s h j next iter
 obtain ⟨value,bound⟩ := NHI_PartialIndex.value offset j side small
 exact ⟨value,bound,by omega,NHE_FieldCanonical.success f _ bound x readx,
  NHM_ArrayCanon.read canonQ q j k hq readq⟩

theorem byte (f : Slice U8) (q : Slice NQ) (hq : NHI_CellCanon.slice q)
 (s : State) (h : NHM_DotLoopDomain.Inv 64 s) (j : Usize) (next : NHI_RangeProgress.Range)
 (iter : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some j,next))
 (x : NE) (k : NQ) (readx : FIo_Native.weights.field f j=ok x)
 (readq : Slice.index_usize q j=ok k) :
 j.val<64 ∧ s.2.count.val<4096 ∧ canonE x ∧ canonQ k := by
 obtain ⟨small,count⟩ := index 64 s h j next iter
 exact ⟨small,by omega,NHE_FieldCanonical.success f j small x readx,
  NHI_CellCanon.slice_read q j k hq readq⟩

#print axioms index
#print axioms high
#print axioms partial
#print axioms byte
end NHM_DotCallDomain
