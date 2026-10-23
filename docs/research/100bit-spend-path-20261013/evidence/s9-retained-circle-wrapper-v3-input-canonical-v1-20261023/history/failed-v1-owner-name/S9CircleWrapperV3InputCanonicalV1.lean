import S9CircleWrapperOutputCanonicalV1
import S9ConstructorV3PointScanBodyCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CircleWrapperV3InputCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1

/-- Structural carrier copy only. This is not a current Rust sampler refinement. -/
def toV3QM (q : AspisR1CircleSampleWrapper.field.QM31) : Q :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def toV3Point (p : AspisR1CircleSampleWrapper.circle.SecureCirclePoint) : Point :=
  ⟨toV3QM p.x,toV3QM p.y⟩

theorem canonical_coordinate_copy (q : AspisR1CircleSampleWrapper.field.QM31)
    (h : AspisV8R19.SamplerClosureProductCorrectness.Canonical
      (AspisR1CircleSampleWrapper.toR72QM q)) : CanQ (toProbeQ (toV3QM q)) := by
  change q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
    q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647 at h
  change (q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647) ∧
    (q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647)
  exact ⟨⟨h.1,h.2.1⟩,⟨h.2.2.1,h.2.2.2⟩⟩

theorem make2_points_canonical (p0 p1 : Point)
    (h0 : CanQ (toProbeQ p0.x) ∧ CanQ (toProbeQ p0.y))
    (h1 : CanQ (toProbeQ p1.x) ∧ CanQ (toProbeQ p1.y)) :
    PointsCanonical (Array.make 2#usize [p0,p1]) := by
  intro k p hread
  have hkbound := index_success_bound (Array.make 2#usize [p0,p1] : Array Point 2#usize) k p hread
  have htwo : (2#usize).val = 2 := by decide
  have hcases : k.val = 0 ∨ k.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hk : k = 0#usize := UScalar.eq_of_val_eq (by simpa using hzero)
    subst k
    change Result.ok p0 = Result.ok p at hread
    have he := Result.ok.inj hread
    rw [← he]
    exact h0
  · have hk : k = 1#usize := UScalar.eq_of_val_eq (by simpa using hone)
    subst k
    change Result.ok p1 = Result.ok p at hread
    have he := Result.ok.inj hread
    rw [← he]
    exact h1

/-- The retained wrapper's two actual returned points, structurally copied to
V3, satisfy the exact circle-input contract consumed by the constructor proof.
Current Rust callee/caller refinement remains a separate explicit obligation. -/
theorem successful_wrapper_pair_supplies_V3_input
    (b0 b1 : Array U8 32#usize)
    (p0 p1 : AspisR1CircleSampleWrapper.circle.SecureCirclePoint)
    (h0 : AspisR1CircleSampleWrapper.sampler.circle_sample b0 .First = .ok p0)
    (h1 : AspisR1CircleSampleWrapper.sampler.circle_sample b1 .Second = .ok p1) :
    PointsCanonical (Array.make 2#usize [toV3Point p0,toV3Point p1]) := by
  have hc0 := AspisR1S9CircleWrapperOutputCanonicalV1.successful_wrapper_circle_coordinates_canonical
    b0 .First p0 h0
  have hc1 := AspisR1S9CircleWrapperOutputCanonicalV1.successful_wrapper_circle_coordinates_canonical
    b1 .Second p1 h1
  exact make2_points_canonical (toV3Point p0) (toV3Point p1)
    ⟨canonical_coordinate_copy p0.x hc0.1,canonical_coordinate_copy p0.y hc0.2⟩
    ⟨canonical_coordinate_copy p1.x hc1.1,canonical_coordinate_copy p1.y hc1.2⟩

#print axioms canonical_coordinate_copy
#print axioms make2_points_canonical
#print axioms successful_wrapper_pair_supplies_V3_input
end AspisR1S9CircleWrapperV3InputCanonicalV1
