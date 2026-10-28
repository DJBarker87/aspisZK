import R1Z.PV_RunJoin_WideImage43
import R1Z.ProverRwP6BodyCandidate
import R1Z.ProverCommitWideQM31Scalar49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideArithmetic44
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
open ProverCommitWideOps48
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev current := ProverRwDictionaryTower.fromW

theorem source_eq (x : Raw) : PV_RunJoin_WideImage43.source x=current (source x) := by
  rfl

theorem add (ops : ExternalFuns) (a b z : Source)
    (h : AspisR1ProducerRelease47.field.wide_exact.WideExact.add a b=.ok z) :
    @aspis_core.field.wide_exact.WideExact.add _ (ProverRwP6BodyCandidate.selected ops)
      (current a) (current b)=.ok (current z) := by
  change mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.add
    (toW (fromW a)) (toW (fromW b)))=_
  rw [native_w_roundtrip,native_w_roundtrip,h]
  rfl

theorem mul (ops : ExternalFuns) (a b z : Source)
    (h : AspisR1ProducerRelease47.field.wide_exact.WideExact.mul a b=.ok z) :
    @aspis_core.field.wide_exact.WideExact.mul _ (ProverRwP6BodyCandidate.selected ops)
      (current a) (current b)=.ok (current z) := by
  change mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul
    (toW (fromW a)) (toW (fromW b)))=_
  rw [native_w_roundtrip,native_w_roundtrip,h]
  rfl

theorem scale (ops : ExternalFuns) (a z : Source) (b : U32)
    (h : AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_m31 a b=.ok z) :
    @aspis_core.field.wide_exact.WideExact.mul_m31 _ (ProverRwP6BodyCandidate.selected ops)
      (current a) b=.ok (current z) := by
  change mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_m31
    (toW (fromW a)) b)=_
  rw [native_w_roundtrip,h]
  rfl
#print axioms source_eq
#print axioms add
#print axioms mul
#print axioms scale
end R1Z.PV_RunJoin_WideArithmetic44
