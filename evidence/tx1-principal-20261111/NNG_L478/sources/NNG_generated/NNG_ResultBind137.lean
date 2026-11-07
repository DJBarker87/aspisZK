import NNG_SourceStep136
import RSL_Verifier
set_option autoImplicit false
namespace AspisR1.NNG_ResultBind137
open NMT_CallTree NNG_Observed136

theorem sound {A B C D E : Type}
    (code : Code A) (k : A → Code B) (headDecode : A → Except E C)
    (outDecode : B → Except E D) (events : NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (head : RSL.RE E C) (tail : C → RSL.RE E D)
    (headLaw : head env (observation headDecode events code))
    (tailLaw : ∀ a, (observation id events code).exit = .ret a →
      (match headDecode a with
      | .ok c => tail c
      | .error e => RSL.Spec.pure (.error e)) env
        (observation outDecode events (k a))) :
    RSL.RE.bind head tail env
      (observation outDecode events (NMT_CallTree.bind code k)) := by
  unfold RSL.RE.bind
  exact NNG_SourceStep136.bind_sound code k headDecode outDecode events env head
    (fun reply => match reply with
      | .ok c => tail c
      | .error e => RSL.Spec.pure (.error e)) headLaw tailLaw
#print axioms sound
end AspisR1.NNG_ResultBind137
