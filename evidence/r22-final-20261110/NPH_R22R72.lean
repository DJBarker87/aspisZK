import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyUnconditionalV1
import RPz7_F3M_CircleSource

/-! NPH_ (R22, R72): the AspisR72Sampler kernels run only inside the wrapper circle sampler.
Definition-level scan (NPH_R72_REFS.json) and the deployed_splitB REACHABLE list:
- every reached R72 kernel call is inside AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
  (through secure_circle_point_from_parameter and the QM31/CM31 towers);
- the reached callers of that function are the wrapper externals (root-namespace
  circle.secure_ood_circle_point_from_parameter and AspisR1CircleFallback.circle.secure_ood...,
  the latter reached only through root transcript.circle_fallback_point ->
  AspisR1CircleFallback.transcript.circle_fallback_point), all of which run only inside
  AspisR1CircleSampleWrapper.sampler.circle_sample (its mapper and its fallback closure);
- the R72-internal transcript loop (challenge_secure_circle_point_loop) is not reached.
`circle_sample_total`: the wrapper sampler is ok for EVERY input block and row (closure theorem
RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle). So every R72 kernel call it
executes returns ok, on every execution, whatever the caller passes. `circle_source_total`: the
same for the deployed finish circle boundary F3M_CircleSource.source (IDa_Deployed.boundaries
circle slot). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22R72
open Aeneas Aeneas.Std Result

theorem circle_sample_total (block : Array U8 32#usize)
    (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
    ∃ p, AspisR1CircleSampleWrapper.sampler.circle_sample block row = ok p := by
  obtain ⟨p, h, _⟩ :=
    AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle block row
  exact ⟨p, h⟩
#print axioms circle_sample_total

theorem circle_source_total (block : Array U8 32#usize)
    (r : AspisR1PublicPreparation.FinishModel.CircleRow) :
    ∃ q, F3M_CircleSource.source block r = ok q := by
  obtain ⟨p, h⟩ := circle_sample_total block (F3M_CircleSource.row r)
  exact ⟨F3M_CircleSource.point p, by simp only [F3M_CircleSource.source, h, bind_tc_ok]⟩
#print axioms circle_source_total

end AspisR1.NPH_R22R72
