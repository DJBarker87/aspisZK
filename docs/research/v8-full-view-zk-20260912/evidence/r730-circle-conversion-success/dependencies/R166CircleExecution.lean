import AspisV8R19.R165QuarticExecution

/-! Exact selected secure-circle conversion on canonical source inputs.
Singular rejection precedes the subfield rejection, and successful coordinates
are canonical and satisfy the circle equation. The transcript sampler is separate. -/
set_option autoImplicit false
namespace AspisV8R19.R166CircleExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open R165QuarticExecution
open R164ProductExecution (encode)
open R163ComplexExecution (cm_zero_test)
noncomputable section

abbrev encodeCM := R163ComplexExecution.encode

def encodePoint (p : QM31Exact × QM31Exact) : circle.SecureCirclePoint :=
  ⟨encode p.1,encode p.2⟩
def decodePoint (p : circle.SecureCirclePoint) : QM31Exact × QM31Exact :=
  (decode p.x,decode p.y)
def encodeError : SamplerCirclePolicy.MapError → circle.CirclePointError
  | .singular => .SingularParameter
  | .subfield => .ParameterInCm31Subfield
def encodeResult : Except SamplerCirclePolicy.MapError (QM31Exact × QM31Exact) →
    core.result.Result circle.SecureCirclePoint circle.CirclePointError
  | .error e => .Err (encodeError e)
  | .ok p => .Ok (encodePoint p)

theorem decode_point (p : QM31Exact × QM31Exact) : decodePoint (encodePoint p) = p := by
  simp only [decodePoint,encodePoint,decode_encode]
theorem point_canonical (p : QM31Exact × QM31Exact) :
    Canonical (encodePoint p).x ∧ Canonical (encodePoint p).y :=
  ⟨encode_canonical _,encode_canonical _⟩
theorem cm_eq_zero (x : CM31Exact) :
    field.CM31.Insts.CoreCmpPartialEqCM31.eq (encodeCM x) field.CM31.ZERO =
      .ok (decide (x = 0)) := by
  have he : field.CM31.Insts.CoreCmpPartialEqCM31.eq (encodeCM x) field.CM31.ZERO =
      field.CM31.is_zero (encodeCM x) := by
    simp only [field.CM31.Insts.CoreCmpPartialEqCM31.eq,field.M31.Insts.CoreCmpPartialEqM31.eq,
      field.CM31.ZERO,field.CM31.is_zero,field.M31.is_zero,bind_tc_ok]
  rw [he,cm_zero_test]

theorem circle_singular (t : QM31Exact) (hd : 1+t*t = 0) :
    circle.secure_circle_point_from_parameter (encode t) =
      .ok (.Err .SingularParameter) := by
  simp only [circle.secure_circle_point_from_parameter,square,one,add,hd,
    try_inverse_zero,bind_tc_ok,AspisR156FullFreeze.core.option.Option.ok_or]
  rfl
theorem circle_regular (t : QM31Exact) (hd : 1+t*t ≠ 0) :
    circle.secure_circle_point_from_parameter (encode t) =
      .ok (.Ok (encodePoint (SamplerCirclePolicy.point t))) := by
  simp only [circle.secure_circle_point_from_parameter,square,one,add,
    try_inverse_nonzero _ hd,bind_tc_ok,AspisR156FullFreeze.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]
  simp only [bind_tc_ok,sub,R164ProductExecution.public_product]
  simp only [encodePoint,SamplerCirclePolicy.point,AspisV8R15.CircleChord.px,
    AspisV8R15.CircleChord.py,pow_two,div_eq_mul_inv,two_mul]

theorem ood_singular (t : QM31Exact) (hd : 1+t*t = 0) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (.Err .SingularParameter) := by
  simp only [circle.secure_ood_circle_point_from_parameter,circle_singular t hd,bind_tc_ok]
  rfl
theorem ood_subfield (t : QM31Exact) (hd : 1+t*t ≠ 0) (ht : t.im = 0) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (.Err .ParameterInCm31Subfield) := by
  simp only [circle.secure_ood_circle_point_from_parameter,circle_regular t hd,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  change (do
    let b ← field.CM31.Insts.CoreCmpPartialEqCM31.eq (encodeCM t.im) field.CM31.ZERO
    if b then ok (core.result.Result.Err circle.CirclePointError.ParameterInCm31Subfield)
      else ok (core.result.Result.Ok (encodePoint (SamplerCirclePolicy.point t)))) = _
  simp only [cm_eq_zero,ht,decide_true,bind_tc_ok,if_true]
theorem ood_outside (t : QM31Exact) (ht : t.im ≠ 0) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (.Ok (encodePoint (SamplerCirclePolicy.point t))) := by
  have hd : 1+t*t ≠ 0 := by
    simpa only [pow_two] using SamplerCirclePolicy.outside_has_denominator t ht
  simp only [circle.secure_ood_circle_point_from_parameter,circle_regular t hd,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  change (do
    let b ← field.CM31.Insts.CoreCmpPartialEqCM31.eq (encodeCM t.im) field.CM31.ZERO
    if b then ok (core.result.Result.Err circle.CirclePointError.ParameterInCm31Subfield)
      else ok (core.result.Result.Ok (encodePoint (SamplerCirclePolicy.point t)))) = _
  simp only [cm_eq_zero,ht,decide_false,bind_tc_ok,Bool.false_eq_true,if_false]

theorem encoded_execution (t : QM31Exact) :
    circle.secure_ood_circle_point_from_parameter (encode t) =
      .ok (encodeResult (SamplerCirclePolicy.pureMap t)) := by
  by_cases hd : 1+t*t = 0
  · rw [ood_singular t hd]
    simp only [SamplerCirclePolicy.pureMap,pow_two,hd,if_true,encodeResult,encodeError]
  · by_cases ht : t.im = 0
    · rw [ood_subfield t hd ht]
      simp only [SamplerCirclePolicy.pureMap,pow_two,hd,ht,if_false,if_true,encodeResult,encodeError]
    · rw [ood_outside t ht,SamplerCirclePolicy.outside_map t ht]
      rfl
theorem source_execution (t : field.QM31) (hc : Canonical t) :
    circle.secure_ood_circle_point_from_parameter t =
      .ok (encodeResult (SamplerCirclePolicy.pureMap (decode t))) := by
  conv_lhs => rw [← encode_decode t hc]
  exact encoded_execution (decode t)
theorem no_failure (t : field.QM31) (hc : Canonical t) (e : Error) :
    circle.secure_ood_circle_point_from_parameter t ≠ .fail e := by
  rw [source_execution t hc]; simp
theorem successful_output (t : field.QM31) (hc : Canonical t)
    (p : circle.SecureCirclePoint)
    (hp : circle.secure_ood_circle_point_from_parameter t = .ok (.Ok p)) :
    (decode t).im ≠ 0 ∧ Canonical p.x ∧ Canonical p.y ∧
      decodePoint p = SamplerCirclePolicy.point (decode t) ∧
      (decode p.x)^2+(decode p.y)^2 = 1 := by
  rw [source_execution t hc] at hp
  cases hm : SamplerCirclePolicy.pureMap (decode t) with
  | error e => simp [hm,encodeResult] at hp
  | ok q =>
    have he : encodePoint q = p := by simpa only [hm,encodeResult,Result.ok.injEq,
      core.result.Result.Ok.injEq] using hp
    obtain ⟨ht,hd,hq⟩ := SamplerCirclePolicy.success_policy _ q hm
    subst p
    refine ⟨ht,(point_canonical q).1,(point_canonical q).2,?_,?_⟩
    · rw [decode_point,hq]
    · change (decode (encode q.1))^2+(decode (encode q.2))^2=1
      rw [decode_encode,decode_encode,hq]
      exact SamplerCirclePolicy.point_on_circle _ hd

#print axioms decode_point
#print axioms point_canonical
#print axioms cm_eq_zero
#print axioms circle_singular
#print axioms circle_regular
#print axioms ood_singular
#print axioms ood_subfield
#print axioms ood_outside
#print axioms encoded_execution
#print axioms source_execution
#print axioms no_failure
#print axioms successful_output
end
end AspisV8R19.R166CircleExecution
