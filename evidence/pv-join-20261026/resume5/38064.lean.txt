import R1Z.PV_Join_ResultInvariant5
set_option autoImplicit false
namespace R1Z.PV_Join_LoopInvariant5
open Aeneas Aeneas.Std Result PV_Join_ResultInvariant5

theorem preserve {α β : Type} (rank : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β))
    (step : ∀ x, inv x → Safe (fun cf => match cf with
      | .done y => post y
      | .cont y => inv y ∧ rank y < rank x) (body x)) :
    ∀ x, inv x → Safe post (loop body x) := by
  have go : ∀ n x, rank x = n → inv x → Safe post (loop body x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn hx
      rw [loop.eq_def]
      cases hb : body x with
      | fail e => intro y hy; cases hy
      | div => intro y hy; cases hy
      | ok cf =>
        cases cf with
        | done y => exact PV_Join_ResultInvariant5.ok post y (step x hx _ hb)
        | cont y =>
          obtain ⟨hy,hr⟩ := step x hx _ hb
          exact ih (rank y) (by omega) y rfl hy
  intro x hx
  exact go (rank x) x rfl hx

#print axioms preserve
end R1Z.PV_Join_LoopInvariant5
