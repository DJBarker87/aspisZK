import NKM_FallbackModel
set_option autoImplicit false
noncomputable section
namespace NKM_Roots
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19 R0P.SemSource
open NKM_circle NKM_FieldLaws NKM_CircleModel
abbrev Reply := core.result.Result NKM_circle.circle.SecureCirclePoint NKM_circle.circle.CirclePointError

/-- K004/K005 exact returned-Result function G; no field operation is executed here. -/
def circleG (inverse : Option NKM_circle.field.QM31) (x y : NKM_circle.field.QM31) : Reply :=
 match inverse with | none => .Err .SingularParameter | some _ => .Ok ⟨x,y⟩

/-- The source-ordered field replies, with every child clause discharged by NKM_FieldLaws. -/
def circleInvocation (t : QM31Exact) : Reply :=
 let d := 1+t*t
 circleG (if d=0 then none else some (encode d⁻¹))
  (encode ((1-t*t)*d⁻¹)) (encode ((t+t)*d⁻¹))

/-- K006/K007 G propagates the full first reply before inspecting the subfield. -/
def oodG (subfield : Bool) (child : Reply) : Reply :=
 match child with | .Err e => .Err e | .Ok p => if subfield then .Err .ParameterInCm31Subfield else .Ok p

def oodInvocation (t : QM31Exact) : Reply := oodG (decide (t.im=0)) (circleInvocation t)

/-- K008/K009 G includes both Err variants; the default point is literal (1,0). -/
def fallbackG (child : Reply) : NKM_circle.circle.SecureCirclePoint :=
 match child with | .Ok p => p | .Err _ => ⟨NKM_circle.field.QM31.ONE,NKM_circle.field.QM31.ZERO⟩

theorem circle (t : QM31Exact) :
 ok (circleInvocation t) = NKM_circle.circle.secure_circle_point_from_parameter (encode t) := by
 rw [circle_total]
 by_cases hd : 1+t*t=0 <;> simp only [circleInvocation,circleG,circleResult,hd,if_true,if_false,point]

theorem ood (t : QM31Exact) :
 ok (oodInvocation t) = NKM_circle.circle.secure_ood_circle_point_from_parameter (encode t) := by
 rw [ood_total]
 by_cases hd : 1+t*t=0
 · simp only [oodInvocation,circleInvocation,circleG,oodG,oodResult,hd,if_true]
 · by_cases ht : t.im=0 <;> simp only [oodInvocation,circleInvocation,circleG,oodG,oodResult,hd,ht,
    decide_true,decide_false,if_true,if_false,Bool.false_eq_true,point]

theorem fallback0 :
 ok (fallbackG (oodInvocation circleFallbackParameter0)) = NKM_circle.transcript.circle_fallback_point 0#usize := by
 have h : oodInvocation circleFallbackParameter0 = .Ok (point circleFallbackParameter0) := by
  apply Result.ok.inj
  rw [ood,←NKM_FallbackModel.parameter0_encode,NKM_FallbackModel.parameter0_output]
 rw [h,NKM_FallbackModel.fallback0]
 rfl

theorem fallback1 :
 ok (fallbackG (oodInvocation circleFallbackParameter1)) = NKM_circle.transcript.circle_fallback_point 1#usize := by
 have h : oodInvocation circleFallbackParameter1 = .Ok (point circleFallbackParameter1) := by
  apply Result.ok.inj
  rw [ood,←NKM_FallbackModel.parameter1_encode,NKM_FallbackModel.parameter1_output]
 rw [h,NKM_FallbackModel.fallback1]
 rfl

theorem circle_on_canonical (t : NKM_circle.field.QM31) (canonical : Canon t) :
 ok (circleInvocation (SamplerClosureProductCorrectness.decode (toQ t))) =
 NKM_circle.circle.secure_circle_point_from_parameter t := by
 rw [circle,roundtrip t canonical]

theorem ood_on_canonical (t : NKM_circle.field.QM31) (canonical : Canon t) :
 ok (oodInvocation (SamplerClosureProductCorrectness.decode (toQ t))) =
 NKM_circle.circle.secure_ood_circle_point_from_parameter t := by
 rw [ood,roundtrip t canonical]

/-- Explicit first rejection: this precedes any subfield observation. -/
theorem singular_first (t : QM31Exact) (singular : 1+t*t=0) :
 oodInvocation t = .Err .SingularParameter := by
 simp only [oodInvocation,circleInvocation,circleG,oodG,singular,if_true]

/-- The deployed caller's row carries only these two indices. No retry/success premise. -/
theorem fallback (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 ok (fallbackG (oodInvocation (match row with | .First => circleFallbackParameter0 | .Second => circleFallbackParameter1))) =
 NKM_circle.transcript.circle_fallback_point (NKM_FallbackModel.index row) := by
 cases row
 · exact fallback0
 · exact fallback1

#print circle
#print ood
#print fallback
#print axioms circle
#print axioms ood
#print axioms fallback0
#print axioms fallback1
#print axioms circle_on_canonical
#print axioms ood_on_canonical
#print axioms singular_first
#print axioms fallback
end NKM_Roots
end
