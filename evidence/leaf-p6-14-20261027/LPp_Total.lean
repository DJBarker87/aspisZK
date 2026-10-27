import LPp_Closure
import LPp_Reachability
import LPp_MapperValues

set_option autoImplicit false
noncomputable section
namespace LPp.Total
open Aeneas Aeneas.Std Result AspisR1CircleSampleWrapper
open AspisV8R19
open SamplerClosureCircleSourceExecution
open SamplerClosureProductCorrectness

def adapt : core.result.Result AspisR72Sampler.circle.SecureCirclePoint
    AspisR72Sampler.circle.CirclePointError →
    core.result.Result circle.SecureCirclePoint circle.CirclePointError
  | .Ok p => .Ok (fromR72Point p)
  | .Err e => .Err (fromR72Error e)

theorem mapper_law (q : field.QM31) (hq : Canonical (toR72QM q)) :
    circle.secure_ood_circle_point_from_parameter q =
      .ok (adapt (encodeResult (SamplerCirclePolicy.pureMap (decode (toR72QM q))))) := by
  unfold circle.secure_ood_circle_point_from_parameter
  rw [source_execution _ hq]
  cases encodeResult (SamplerCirclePolicy.pureMap (decode (toR72QM q))) <;> rfl

-- Every caller block and both rows; canonicality is DERIVED, not assumed.
-- The value uses the exact sampled parameter from the SAME wrapper call.
theorem circle_sample_exact (block : Array Std.U8 32#usize)
    (row : r0_transcript.CircleRow) :
    ∃ q : field.QM31, sampler.qm31_sample block = .ok q ∧
      Canonical (toR72QM q) ∧
      sampler.circle_sample block row = .ok
        (LPp.Closure.resolve
          (adapt (encodeResult (SamplerCirclePolicy.pureMap (decode (toR72QM q))))) row) := by
  obtain ⟨q, hq, hc⟩ := LPp.Closure.sampler_domain block
  exact ⟨q, hq, hc, LPp.Closure.native_step block row q _ hq (mapper_law q hc)⟩

#print axioms mapper_law
#print axioms circle_sample_exact
end LPp.Total
