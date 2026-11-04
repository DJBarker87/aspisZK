import NGO_NativeTrace
import NGO_TraceInputs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_LiftTrace
open NGD_DecodeTrace AspisR1DecodeKFullV10 NGO_ScheduleState
/-- Construct the original chunks/enumerate trace from every emitted finite
trace, preserving identical store values and the first-error terminal. -/
theorem lift {N : Usize} {r : Record} {off start : Usize}
    (d : Domain N r off start) (original : CE)
    (values : original.chunks.map (fun c=>c.val)=
      NGO_ChunkSchedule.windows (((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) N.val)
    (length : original.chunks.length=N.val)
    (iter : Range) (out : Array Q N) (final : Final N) (trace : Trace d iter out final)
    (finish : iter.end=N) (bounded : iter.start.val≤N.val) :
    NGO_NativeTrace.Run d (state original iter.start) out final := by
  induction trace with
  | done iter out next =>
    have equal : iter.start.val=N.val := by
      by_contra notEqual
      have live : iter.start.val< iter.end.val := by rw [finish];omega
      obtain ⟨⟨o,it⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_some_spec
          (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
          (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl) iter live)
      rw [next] at run
      have same := congrArg Prod.fst (Result.ok.inj run)
      simp_all
    exact NGO_NativeTrace.Run.done _ out (NGO_ScheduleState.stop original iter.start (length.trans equal.symm))
  | reject iter nextIter index out live next error reply =>
    obtain ⟨indexEq,advance,sameEnd,active⟩ := NGO_IteratorIndex.from_some iter nextIter index next
    subst index
    obtain ⟨chunk,native,chunkEq⟩ := NGO_ScheduleState.step original iter.start N nextIter.start length live advance
    have low := NGO_TraceInputs.selected d original values length iter.start live
    rw [chunkEq] at low
    exact NGO_NativeTrace.Run.reject _ _ out iter.start chunk live native low error reply
  | write iter nextIter index out updated live next q reply store final rest ih =>
    obtain ⟨indexEq,advance,sameEnd,active⟩ := NGO_IteratorIndex.from_some iter nextIter index next
    subst index
    obtain ⟨chunk,native,chunkEq⟩ := NGO_ScheduleState.step original iter.start N nextIter.start length live advance
    have low := NGO_TraceInputs.selected d original values length iter.start live
    rw [chunkEq] at low
    exact NGO_NativeTrace.Run.write _ _ out updated iter.start chunk live native low q reply store final
      (ih (sameEnd.trans finish) (by omega))
#print axioms lift
end NGO_LiftTrace
