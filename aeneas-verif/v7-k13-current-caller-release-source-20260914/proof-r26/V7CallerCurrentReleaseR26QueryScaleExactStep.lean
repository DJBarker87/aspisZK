import V7CallerCurrentReleaseR26FieldBridge
import V7CallerCurrentReleaseR26QueryScaleLoop

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryScaleExactStep

open V7CallerCurrentReleaseR26FieldBridge

/-- A successful source iteration of the shifted-query scale loop has the
exact multiplicative meaning required for the rho-power covector.  This keeps
the generated iterator transition symbolic while using the source-authentic
prepared multiplier semantics. -/
theorem scale_loop_body_step_exact
    (rho prior next : field.QM31)
    (prepared : field.PreparedQm31Multiplier)
    (iter iterNext : core.ops.range.Range Std.Usize)
    (scales scalesNext : Array field.QM31 16#usize)
    (ordinal predecessor : Std.Usize)
    (hrho : GeneratedCanonicalQM31 rho)
    (hprior : GeneratedCanonicalQM31 prior)
    (hnew : field.PreparedQm31Multiplier.impl.new rho = ok prepared)
    (hNext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some ordinal, iterNext))
    (hPredecessor : Std.Usize.wrapping_sub ordinal 1#usize = predecessor)
    (hIndex : Array.index_usize scales predecessor = ok prior)
    (hMultiply : field.PreparedQm31Multiplier.impl.mul prepared prior = ok next)
    (hUpdate : Array.update scales ordinal next = ok scalesNext) :
    GeneratedCanonicalQM31 next ∧
      generatedQm31ToExact next =
        generatedQm31ToExact rho * generatedQm31ToExact prior ∧
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
          prepared iter scales = ok (cont (iterNext, scalesNext)) := by
  obtain ⟨hcanonical, hexact⟩ := generated_prepared_qm31_mul_exact rho prior next
    prepared hrho hprior hnew hMultiply
  exact ⟨hcanonical, hexact,
    V7CallerCurrentReleaseR26QueryScaleLoop.scale_loop_body_step prepared iter
      iterNext scales scalesNext ordinal predecessor prior next hNext hPredecessor
      hIndex hMultiply hUpdate⟩

#print axioms scale_loop_body_step_exact

end V7CallerCurrentReleaseR26QueryScaleExactStep
