import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RunJoin_Follows
open Aeneas Aeneas.Std Result

/-- Successful larger executions force the smaller source-prefix result.
No returned world is invented for failure/divergence of the larger execution. -/
def Follows {A B : Type} (project : B → A) (small : Result A) (large : Result B) : Prop :=
  ∀ b, large = .ok b → small = .ok (project b)

theorem returned {A B : Type} (project : B → A) (b : B) :
    Follows project (.ok (project b)) (.ok b) := by
  intro out same
  cases same
  rfl

theorem bind_common {A B C : Type} (project : C → B) (initialResult : Result A)
    (small : A → Result B) (large : A → Result C)
    (follows : ∀ a, Follows project (small a) (large a)) :
    Follows project (initialResult >>= small) (initialResult >>= large) := by
  cases initialResult with
  | fail e => intro out same; cases same
  | div => intro out same; cases same
  | ok a => exact follows a

theorem continuation {A B C : Type} (project : B → A) (final : C → A)
    (small : Result A) (middle : Result B) (large : B → Result C)
    (prefixLaw : Follows project small middle)
    (frame : ∀ b c, large b = .ok c → final c = project b) :
    Follows final small (middle >>= large) := by
  intro c run
  obtain ⟨b,called,after⟩ := PV_RunJoin_ResultPost.bind_eq_ok run
  rw [frame b c after]
  exact prefixLaw b called

#print axioms returned
#print axioms bind_common
#print axioms continuation
end R1Z.PV_RunJoin_Follows
