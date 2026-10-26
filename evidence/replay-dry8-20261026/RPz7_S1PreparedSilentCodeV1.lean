import RPz7_S1PreparedOracleProgramLawsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result
open AspisV8R19.MemoizedProgramLaw

def Silent {A : Type} : Code A → Prop
  | .done _ => True
  | .step _ next => ∀ a, Silent (next a)
  | .digest _ _ _ _ => False

theorem silent_pure {A : Type} (a : A) : Silent (pure a : Code A) := True.intro

theorem silent_lift {A : Type} (r : Result A) : Silent (monadLift r : Code A) := fun _ => True.intro

theorem silent_bind {A B : Type} (p : Code A) (k : A → Code B)
    (hp : Silent p) (hk : ∀ a, Silent (k a)) : Silent (p >>= k) := by
  induction p with
  | done a => exact hk a
  | step r next ih => exact fun a => ih a (hp a)
  | digest D hash parts next ih => exact False.elim hp

/-- Exact no-read interpretation of the explicit syntax, preserving all
Result failures/divergence. Purity of unextracted native callees is not inferred. -/
theorem oracleProgram_silent {A : Type} (p : Code A) (silent : Silent p) :
    oracleProgram p=Program.done (erase p) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok a => exact ih a (silent a)
    | fail e => rfl
    | div => rfl
  | digest D hash parts next ih => exact False.elim silent

#print axioms silent_bind
#print axioms oracleProgram_silent
end AspisR1PublicPreparation.PreparedHashCode
