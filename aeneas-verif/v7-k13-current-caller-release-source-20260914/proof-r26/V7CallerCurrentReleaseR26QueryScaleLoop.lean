import V7CallerCurrentReleaseR26.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseR26QueryScaleLoop

open V7CallerCurrentReleaseR26

/-- One successful iteration of the current source's query-scale loop copies
the prepared multiplication of the preceding scale into the next ordinal and
advances only the range iterator.  The fifteen-step shifted covector proof is
assembled from this symbolic transition rather than by reducing the loop. -/
theorem scale_loop_body_step
    (prepared : field.PreparedQm31Multiplier)
    (iter iterNext : core.ops.range.Range Std.Usize)
    (scales scalesNext : Array field.QM31 16#usize)
    (ordinal predecessor : Std.Usize)
    (prior next : field.QM31)
    (hNext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some ordinal, iterNext))
    (hPredecessor : Std.Usize.wrapping_sub ordinal 1#usize = predecessor)
    (hIndex : Array.index_usize scales predecessor = ok prior)
    (hMultiply : field.PreparedQm31Multiplier.impl.mul prepared prior = ok next)
    (hUpdate : Array.update scales ordinal next = ok scalesNext) :
    v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
        prepared iter scales = ok (cont (iterNext, scalesNext)) := by
  simp only [v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body]
  rw [hNext]
  simp only [bind_tc_ok]
  simp only [lift, hPredecessor, bind_tc_ok]
  rw [hIndex]
  simp only [bind_tc_ok]
  rw [hMultiply]
  simp only [bind_tc_ok]
  rw [hUpdate]
  rfl

/-- The same loop returns its accumulated scale array unchanged once its
range iterator is exhausted. -/
theorem scale_loop_body_done
    (prepared : field.PreparedQm31Multiplier)
    (iter iterNext : core.ops.range.Range Std.Usize)
    (scales : Array field.QM31 16#usize)
    (hNext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (none, iterNext)) :
    v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
        prepared iter scales = ok (done scales) := by
  simp only [v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body]
  rw [hNext]
  rfl

#print axioms scale_loop_body_step
#print axioms scale_loop_body_done

end V7CallerCurrentReleaseR26QueryScaleLoop
