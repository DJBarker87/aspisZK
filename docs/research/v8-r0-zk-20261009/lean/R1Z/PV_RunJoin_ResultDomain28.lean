import R1Z.PV_Src_ResultControl
import R1Z.BuilderRecordsFields
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultDomain28
open Aeneas Aeneas.Std Result

def wp {α : Type} (m : Result α) (p : α → Prop) : Prop :=
  ∃ a, m = ok a ∧ p a

theorem bind_wp {α β : Type} (m : Result α) (f : α → Result β) (p : β → Prop) :
    wp (do let a ← m; f a) p ↔ ∃ a, m = ok a ∧ wp (f a) p := by
  constructor
  · rintro ⟨b,hb,pb⟩
    obtain ⟨a,ha,hf⟩ := R1Z.BuilderRecordsFields.bind_ok_inv hb
    exact ⟨a,ha,b,hf,pb⟩
  · rintro ⟨a,ha,b,hf,pb⟩
    exact ⟨b,by rw [ha]; exact hf,pb⟩
#print axioms bind_wp

theorem ok_wp {α : Type} (a : α) (p : α → Prop) : wp (ok a) p ↔ p a := by
  constructor
  · rintro ⟨b,hb,pb⟩
    cases Result.ok.inj hb
    exact pb
  · exact fun h => ⟨a,rfl,h⟩
#print axioms ok_wp

def isRustOk {α ε : Type} (r : core.result.Result α ε) : Prop := ∃ a, r = .Ok a

theorem isRustOk_ok {α ε : Type} (a : α) : isRustOk (ε := ε) (.Ok a) ↔ True := by
  exact ⟨fun _ => trivial,fun _ => ⟨a,rfl⟩⟩
#print axioms isRustOk_ok

theorem isRustOk_err {α ε : Type} (e : ε) : isRustOk (α := α) (.Err e) ↔ False := by
  constructor
  · rintro ⟨a,h⟩; cases h
  · exact False.elim
#print axioms isRustOk_err

theorem residual_wp {α ε : Type} (r : core.result.Result core.convert.Infallible ε) :
    wp (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      α (core.convert.FromSame ε) r) isRustOk ↔ False := by
  constructor
  · rintro ⟨s,hs,a,ha⟩
    subst s
    exact PV_Src_ResultControl.same_residual_ne_ok r a hs
  · exact False.elim
#print axioms residual_wp

theorem success_wp {α ε : Type} (m : Result (core.result.Result α ε)) :
    (∃ a, m = ok (.Ok a)) ↔ wp m isRustOk := by
  constructor
  · rintro ⟨a,h⟩; exact ⟨.Ok a,h,a,rfl⟩
  · rintro ⟨s,hs,a,ha⟩; subst s; exact ⟨a,hs⟩
#print axioms success_wp
end R1Z.PV_RunJoin_ResultDomain28
