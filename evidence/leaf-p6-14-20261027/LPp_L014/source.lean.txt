import LPp_Inverse

set_option autoImplicit false
noncomputable section
namespace LPp.Reachability
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open AspisV8R19
open SamplerClosureProductExecution (encode)

def pole : QM31Exact := ⟨⟨0,1⟩,0⟩

theorem pole_denominator : 1+pole*pole = 0 := by decide

theorem pole_reaches_singular :
    circle.secure_ood_circle_point_from_parameter (encode pole) =
      .ok (.Err .SingularParameter) :=
  LPp.singular_arm pole pole_denominator

-- A singular denominator cannot occur outside the rejected subfield.
theorem singular_in_subfield (t : QM31Exact) (hd : 1+t*t = 0) : t.im = 0 := by
  by_contra ht
  exact (SamplerCirclePolicy.outside_has_denominator t ht) (by simpa only [pow_two] using hd)

theorem error_iff_subfield (t : QM31Exact) :
    (∃ e, circle.secure_ood_circle_point_from_parameter (encode t) = .ok (.Err e)) ↔ t.im = 0 := by
  constructor
  · rintro ⟨e, he⟩
    by_contra ht
    rw [SamplerClosureCircleSourceExecution.ood_outside t ht] at he
    cases he
  · intro ht
    by_cases hd : 1+t*t = 0
    · exact ⟨_, LPp.singular_arm t hd⟩
    · exact ⟨_, LPp.subfield_arm t hd ht⟩

#print axioms pole_denominator
#print axioms pole_reaches_singular
#print axioms singular_in_subfield
#print axioms error_iff_subfield
end LPp.Reachability
