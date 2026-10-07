import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy
import AspisV8R19.DistinctCircleProgram

/-! Source policy distinction: successful R609 circle outcomes exclude the
CM31 subfield, hence exclude BaseRational. Abort outcomes remain explicit;
this is not a total sampler law or a composition theorem. -/
set_option autoImplicit false
namespace R0C.CircleSource
open AspisR0.Chord AspisR0.ChordGeometry AspisCircleGroupOrder
open AspisV8R15.ExactTowerBase AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
noncomputable section

/-- Base-field points lie in CM31 in both coordinates. -/
theorem rational_im_zero (z : Point QM31Exact) (hz : BaseRational z) :
    z.val.1.im = 0 ∧ z.val.2.im = 0 := by
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := hz
  rw [← hx, ← hy]
  constructor <;> rfl

/-- The successful parameter policy is stronger than R0's non-rational test. -/
theorem parameter_not_rational (t : QM31Exact) (ht : t.im ≠ 0) :
    ¬ BaseRational (⟨point t, point_on_circle t (outside_has_denominator t ht)⟩ :
      Point QM31Exact) := by
  intro h
  exact outside_point t ht (rational_im_zero _ h)

/-- Applies to the literal bounded source-shaped run, on its success branch. -/
theorem source_success_not_rational (H : Bytes → State) (s : State)
    (z : Point QM31Exact) (h : (circleRun H s).2.1 = .ok z.val) :
    ¬ BaseRational z := by
  obtain ⟨xs,_,_,hout,hp,_⟩ := circle_result H s z.val h
  intro hz
  have hi := rational_im_zero z hz
  rw [hp] at hi
  exact outside_point _ hout hi


/-- Same success fact with the actual source error constructors. -/
theorem model_success_not_rational (H : Bytes → State) (n : Nat) (s : State)
    (z : Point QM31Exact)
    (h : (AspisV8R19.SamplerCircleBridge.modelRun H n s).2.1 = .ok z.val) :
    ¬ BaseRational z := by
  obtain ⟨xs,_,_,ha⟩ := AspisV8R19.BoundedSamplerWrapper.successful_image _ _ _ H n s z.val h
  obtain ⟨hout,_,hp⟩ := accept_policy xs z.val ha
  intro hz
  have hi := rational_im_zero z hz
  rw [hp] at hi
  exact outside_point _ hout hi

/-- The bounded distinct-second wrapper enforces both tests on success.
Its exhaustion branch is not assigned a default point. -/
theorem distinct_success_conditions (H : Bytes → State) (first : QM31Exact × QM31Exact)
    (n : Nat) (s : State) (z : Point QM31Exact)
    (h : (AspisV8R19.DistinctCircleProgram.run H first n s).2.1 = .ok z.val) :
    z.val ≠ first ∧ ¬ BaseRational z := by
  induction n generalizing s with
  | zero => cases h
  | succ n ih =>
      simp only [AspisV8R19.DistinctCircleProgram.run] at h
      generalize hr : AspisV8R19.SamplerCircleBridge.modelRun H 3 s = r at h
      rcases r with ⟨tr,out,t⟩
      cases out with
      | error e => cases h
      | ok p =>
          by_cases he : p = first
          · simp only [he, if_true] at h
            exact ih t h
          · simp only [he, if_false] at h
            have hp : p = z.val := Except.ok.inj h
            subst p
            exact ⟨he, model_success_not_rational H 3 s z (by rw [hr])⟩

#print axioms model_success_not_rational
#print axioms distinct_success_conditions

#print axioms parameter_not_rational
#print axioms source_success_not_rational
end
end R0C.CircleSource
