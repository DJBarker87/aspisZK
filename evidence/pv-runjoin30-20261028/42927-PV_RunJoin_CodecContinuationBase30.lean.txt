import R1Z.PV_RunJoin_ResultDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CodecContinuationBase30
open Aeneas Aeneas.Std Result PV_RunJoin_ResultDomain28

def accepts {α ε : Type} (post : α → Prop) : core.result.Result α ε → Prop
  | .Ok a => post a
  | .Err _ => False

theorem wp_accepts {α ε : Type} (post : α → Prop) (m : Result (core.result.Result α ε)) :
    wp m (accepts post) ↔ ∃ a, m = ok (.Ok a) ∧ post a := by
  constructor
  · rintro ⟨r,hr,hp⟩
    cases r with
    | Ok a => exact ⟨a,hr,hp⟩
    | Err e => cases hp
  · rintro ⟨a,ha,hp⟩
    exact ⟨.Ok a,ha,hp⟩
#print axioms wp_accepts

theorem residual_accepts {α ε : Type} (post : α → Prop)
    (r : core.result.Result core.convert.Infallible ε) :
    wp (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      α (core.convert.FromSame ε) r) (accepts post) ↔ False := by
  constructor
  · rintro ⟨s,hs,hp⟩
    cases s with
    | Ok a => exact PV_Src_ResultControl.same_residual_ne_ok r a hs
    | Err e => cases hp
  · exact False.elim
#print axioms residual_accepts
end R1Z.PV_RunJoin_CodecContinuationBase30
