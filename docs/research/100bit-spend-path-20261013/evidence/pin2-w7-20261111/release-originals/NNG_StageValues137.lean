import NNG_PublicProjection137
import NNG_BeginProjection137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_StageValues137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport

theorem public_eval (env : RSL.Env) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix)
    (t : r1_wire.SemanticTranscript Unit)
    (returned : NMP_Install131.publicTranscript (NNG_PublicSource137.digest env) (fromT9 pub) ()
      (fromT13 (LIB_VCarriers.prefixRaw p)).c1_root = .ok (.Ok t)) :
    LIB_VPublicTranscript.eval (pub,LIB_VCarriers.c1Root p) env=.ok (toT10 t) := by
  have value := NNG_PublicProjection137.projected env pub p
  rw [returned] at value
  have code := LIB_VPublicTranscript.source (pub,LIB_VCarriers.c1Root p) env
  unfold LIB_VPublicTranscript.eval
  rw [code]
  generalize h : (AspisR1PublicPreparation.PreparedHashCode.run
    (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) pub ()
      (LIB_Env.nativeKey (LIB_VCarriers.c1Root p)))).2 = reply at value ⊢
  cases reply with
  | fail e=>cases value
  | div=>cases value
  | ok r=>
    cases r with
    | Err e=>cases value
    | Ok after=>
      have same := Except.ok.inj (Result.ok.inj value)
      exact congrArg Except.ok same.symm
#print axioms public_eval

theorem begin_eval (fallback : LIB_VCarriers.QM31) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (t : r1_wire.SemanticTranscript Unit) (c : aspis_core.state_only_prefix.r0.Challenges)
    (after : r1_wire.SemanticTranscript Unit)
    (returned : NMP_Install150.begin_ (NNG_PublicSource137.digest env) (fromT13 (LIB_VCarriers.prefixRaw p)) t = .ok (.Ok c,after)) :
    LIB_VBegin.eval (p,toT10 t) env = .ok (NNG_ChallengeProjection137.project fallback (toT3 c),toT10 after) := by
  have value := NNG_BeginProjection137.projected fallback env p (toT10 t)
  rw [toT10_inverse,returned] at value
  unfold LIB_VBegin.eval
  rw [←value]
  rfl
#print axioms begin_eval
end AspisR1.NNG_StageValues137
