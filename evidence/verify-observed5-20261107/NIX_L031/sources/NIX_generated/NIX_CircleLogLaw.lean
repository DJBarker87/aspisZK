import NIH_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_CircleLogLaw
open Aeneas Aeneas.Std Result AspisR72Sampler
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductExecution (encode)
open AspisV8R19.SamplerClosureProductCorrectness (Canonical decode encode_canonical encode_decode public_product)
open AspisV8R19.SamplerClosureCircleFieldExecution
abbrev Q := AspisR72Sampler.field.QM31
abbrev Point := AspisR72Sampler.circle.SecureCirclePoint
abbrev Err := AspisR72Sampler.circle.CirclePointError
structure Replies where
 square : Q
 denominator : Q
 inverse : Option Q
 difference : Q
 x : Q
 twice : Q
 y : Q
/-- Callee laws for the SAME logged operands of NIX_circle::rational_map.
No successful mapper or caller return is a premise. -/
def Law (q : Q) (r : Replies) : Prop :=
 field.QM31.square q=ok r.square ∧
 field.QM31.add field.QM31.ONE r.square=ok r.denominator ∧
 field.QM31.try_inv r.denominator=ok r.inverse ∧
 ∀ v,r.inverse=some v →
 field.QM31.sub field.QM31.ONE r.square=ok r.difference ∧
 field.QM31.mul r.difference v=ok r.x ∧
 field.QM31.add q q=ok r.twice ∧
 field.QM31.mul r.twice v=ok r.y

def reply (r : Replies) : core.result.Result Point Err :=
 match r.inverse with
 | none=>.Err .SingularParameter
 | some _=>.Ok ⟨r.x,r.y⟩

/-- Exact full RustResult, including the singular arm and its absent suffix. -/
theorem source_of_log (q : Q) (r : Replies) (law : Law q r) :
 circle.secure_circle_point_from_parameter q=ok (reply r) := by
 rcases law with ⟨sq,den,inv,tail⟩
 simp only [circle.secure_circle_point_from_parameter,sq,den,inv,bind_tc_ok]
 cases h : r.inverse with
 | none=>simp only [h,AspisR72Sampler.core.option.Option.ok_or,reply,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
 | some v=>
   obtain ⟨sub,mx,twice,my⟩:=tail v h
   simp [h,AspisR72Sampler.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,sub,mx,twice,my,reply]

def modelReplies (t : QM31Exact) : Replies where
 square:=encode (t*t)
 denominator:=encode (1+t*t)
 inverse:=if 1+t*t=0 then none else some (encode ((1+t*t)⁻¹))
 difference:=encode (1-t*t)
 x:=encode ((1-t*t)*(1+t*t)⁻¹)
 twice:=encode (t+t)
 y:=encode ((t+t)*(1+t*t)⁻¹)

theorem encoded_law (t : QM31Exact) : Law (encode t) (modelReplies t) := by
 simp only [Law,modelReplies]
 refine ⟨square t,?_,?_,?_⟩
 · rw [one];exact add 1 (t*t)
 · by_cases singular : 1+t*t=0
   · rw [if_pos singular,singular];exact try_inverse_zero
   · rw [if_neg singular];exact try_inverse_nonzero _ singular
 · intro v selected
   by_cases singular : 1+t*t=0
   · simp only [if_pos singular] at selected;cases selected
   · rw [if_neg singular] at selected
     cases Option.some.inj selected
     refine ⟨?_,public_product _ _,add t t,public_product _ _⟩
     rw [one];exact sub 1 (t*t)

def Domain (q : Q) (r : Replies) : Prop :=
 Canonical q ∧ Canonical r.square ∧ Canonical r.denominator ∧
 Canonical r.difference ∧ Canonical r.x ∧ Canonical r.twice ∧ Canonical r.y ∧
 ∀ v,r.inverse=some v → Canonical v

theorem encoded_domain (t : QM31Exact) : Domain (encode t) (modelReplies t) := by
 refine ⟨encode_canonical _,encode_canonical _,encode_canonical _,encode_canonical _,
  encode_canonical _,encode_canonical _,encode_canonical _,?_⟩
 intro v selected
 by_cases singular : 1+t*t=0
 · simp only [modelReplies,if_pos singular] at selected;cases selected
 · simp only [modelReplies,if_neg singular,Option.some.injEq] at selected
   subst v;exact encode_canonical _

/-- All native stub domains are DERIVED on canonical input, not added as mapper-success assumptions. -/
theorem packet (q : Q) (canonical : Canonical q) :
 ∃ r,Law q r ∧ Domain q r ∧ circle.secure_circle_point_from_parameter q=ok (reply r) := by
 have same : encode (decode q)=q := encode_decode q canonical
 refine ⟨modelReplies (decode q),?_,?_,?_⟩
 · rw [←same];simpa only [AspisV8R19.SamplerClosureProductCorrectness.decode_encode] using encoded_law (decode q)
 · rw [←same];simpa only [AspisV8R19.SamplerClosureProductCorrectness.decode_encode] using encoded_domain (decode q)
 · apply source_of_log
   rw [←same];simpa only [AspisV8R19.SamplerClosureProductCorrectness.decode_encode] using encoded_law (decode q)

#print axioms source_of_log
#print axioms encoded_law
#print axioms encoded_domain
#print axioms packet
end AspisR1.NIX_CircleLogLaw
end
