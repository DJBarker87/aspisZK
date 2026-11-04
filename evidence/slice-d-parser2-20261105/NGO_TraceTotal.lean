import NGD_DecodeEntry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_TraceTotal
open AspisR1DecodeKFullV10 NGD_DecodeTrace
/-- Construct the finite emitted trace from any input and any framed prestate.
No trace, accepted outcome, or canonicality premise is supplied by the caller. -/
theorem exists_trace {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (iter : Range) (out : Array Q N)
    (finish : iter.end = N) (bounded : iter.start.val ≤ N.val) :
    ∃ final, Trace d iter out final := by
  generalize hm : N.val-iter.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing iter out with
  | h remaining ih =>
    by_cases live : iter.start.val < N.val
    · obtain ⟨⟨o,nextIter⟩,next,ho,hs,he⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_some_spec
          (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
          (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
          iter (by rw [finish];exact live))
      subst o
      cases reply : answer d iter.start live with
      | Err error => exact ⟨_,Trace.reject iter nextIter iter.start out live next error reply⟩
      | Ok q =>
        obtain ⟨updated,store,post⟩ := WP.spec_imp_exists
          (Array.update_spec out iter.start q (by simpa only [out.property] using live))
        obtain ⟨final,rest⟩ := ih (N.val-nextIter.start.val) (by omega)
          nextIter updated (he.trans finish) (by omega) rfl
        exact ⟨final,Trace.write iter nextIter iter.start out updated live next q reply store final rest⟩
    · obtain ⟨⟨o,iter1⟩,next,ho,hi⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_none_spec
          (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
          (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl)
          iter (by rw [finish];omega))
      subst o;subst iter1
      exact ⟨_,Trace.done iter out next⟩
#print axioms exists_trace
end NGO_TraceTotal
