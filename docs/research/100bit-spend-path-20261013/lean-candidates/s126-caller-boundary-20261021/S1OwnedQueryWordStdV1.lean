import S1OwnedQueryContainsStdV1
import S1OwnedQueryBlockTotalV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result

/-- Complete word transition using the same concrete prefix-read and membership
operations as the retained emitted scanner body; all buffer fields are kept. -/
def stdWord (a : Array U32 22#usize) (len draws : Usize) (candidate : U32) :
    Result AspisS1OwnedQueryBlock.Total.Output := do
  if len=22#usize then ok (a,len,draws,true)
  else if draws=64#usize then ok (a,len,draws,true)
  else
    let d ← draws+1#usize
    let sl ← core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      a {«end»:=len}
    let found ← core.slice.Slice.contains core.cmp.PartialEqU32 sl candidate
    if found then ok (a,len,d,false)
    else
      let updated ← Array.update a len candidate
      let n ← len+1#usize
      ok (updated,n,d,false)

/-- Full Result equality, including every ordinary failure/divergence of the
concrete Std operations. Prefix/membership success is derived, not assumed. -/
theorem owned_step_eq_stdWord (a : Array U32 22#usize) (len draws : Usize)
    (candidate : U32) (hlen : len.val≤22) :
    owned_step a len draws candidate=stdWord a len draws candidate := by
  by_cases full : len=22#usize
  · simp only [owned_step,stdWord,if_pos full]
  by_cases exhausted : draws=64#usize
  · simp only [owned_step,stdWord,if_neg full,if_pos exhausted]
  have bound : len.val≤a.length := by simp only [Array.length,a.property];exact hlen
  have prefixSpec := core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    ({«end»:=len} : core.ops.range.RangeTo Usize) (Array.to_slice a) bound
  obtain ⟨sl,read,spec⟩ := WP.spec_imp_exists prefixSpec
  have frame : sl.val=a.val.take len.val := by
    rcases spec with ⟨value,_⟩
    simpa [Array.to_slice,List.slice] using value
  have read' : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      a {«end»:=len}=ok sl := read
  simp only [owned_step,stdWord,if_neg full,if_neg exhausted]
  apply bind_congr
  intro d
  rw [read']
  simp only [bind_tc_ok]
  rw [contains_eq_std a len candidate sl hlen frame]

/-- Existing complete-source word interpretation inherits TOTAL range safety
without adding successful-prefix/membership/update premises. -/
theorem stdWord_total (a : Array U32 22#usize) (len draws : Usize) (candidate : U32)
    (hlen : len.val≤22) (hd : draws.val≤64) :
    ∃ out, stdWord a len draws candidate=ok out ∧ AspisS1OwnedQueryBlock.Total.validOutput out := by
  obtain ⟨a',l,d,stop,call,hl,hd'⟩ := AspisS1OwnedQueryBlock.Total.step_total a len draws candidate hlen hd
  rw [owned_step_eq_stdWord a len draws candidate hlen] at call
  exact ⟨(a',l,d,stop),call,hl,hd'⟩

#print axioms owned_step_eq_stdWord
#print axioms stdWord_total
end AspisS1OwnedQueryBlock.Meaning
