import NBL_CodeRunLaws
set_option autoImplicit false
namespace AspisR1.NBL_QuietRun
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

/-- A lifted non-oracle step contributes no event, on success, fail and div. -/
theorem bind {A B : Type} (r : Result A) (k : A → Code B) (f : A → Result B)
    (next : ∀ a,run (k a)=([],f a)) :
    run ((monadLift r : Code A) >>= k)=([],r >>= f) := by
  rw [bind_run,lift_run]
  cases r with
  | ok a => simp only [chain,next,List.nil_append,bind_tc_ok]
  | fail e => rfl
  | div => rfl

#print axioms bind
end AspisR1.NBL_QuietRun
