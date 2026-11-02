import PV_B3P_PanicPatterns571227
namespace PV_B3P_PatternFamilies571227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false
/-- 468 inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem index_out_of_bounds_family {α State : Type} (state : Fin 468 → State → IndexState)
    (actual : Fin 468 → State → Prop)
    (guards : ∀ site s, actual site s → (indexGuard) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic ((indexGuard) (state site s)) ∧
      branch ((indexGuard) (state site s)) normal first =
        branch ((indexGuard) (state site s)) normal second := by
  intro site s reached
  exact (index_out_of_bounds (state site s) normal first second).2 (guards site s reached)
#print axioms index_out_of_bounds_family
/-- 19 inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem arithmetic_overflow_family {α State : Type} (state : Fin 19 → State → ArithmeticState)
    (actual : Fin 19 → State → Prop)
    (guards : ∀ site s, actual site s → (arithmeticGuard) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic ((arithmeticGuard) (state site s)) ∧
      branch ((arithmeticGuard) (state site s)) normal first =
        branch ((arithmeticGuard) (state site s)) normal second := by
  intro site s reached
  exact (arithmetic_overflow (state site s) normal first second).2 (guards site s reached)
#print axioms arithmetic_overflow_family
/-- 3 inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem unwrap_expect_family {α State : Type} (state : Fin 3 → State → Option Unit)
    (actual : Fin 3 → State → Prop)
    (guards : ∀ site s, actual site s → (optionGuard) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic ((optionGuard) (state site s)) ∧
      branch ((optionGuard) (state site s)) normal first =
        branch ((optionGuard) (state site s)) normal second := by
  intro site s reached
  exact (unwrap_expect (state site s) normal first second).2 (guards site s reached)
#print axioms unwrap_expect_family
/-- 7 inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem explicit_panic_family {α State : Type} (state : Fin 7 → State → Bool)
    (actual : Fin 7 → State → Prop)
    (guards : ∀ site s, actual site s → (fun b => b = true) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic ((fun b => b = true) (state site s)) ∧
      branch ((fun b => b = true) (state site s)) normal first =
        branch ((fun b => b = true) (state site s)) normal second := by
  intro site s reached
  exact (explicit_panic (state site s) normal first second).2 (guards site s reached)
#print axioms explicit_panic_family
/-- 31 inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem assertion_family {α State : Type} (state : Fin 31 → State → Bool × Bool)
    (actual : Fin 31 → State → Prop)
    (guards : ∀ site s, actual site s → (fun b : Bool × Bool => b.1 = b.2) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic ((fun b : Bool × Bool => b.1 = b.2) (state site s)) ∧
      branch ((fun b : Bool × Bool => b.1 = b.2) (state site s)) normal first =
        branch ((fun b : Bool × Bool => b.1 = b.2) (state site s)) normal second := by
  intro site s reached
  exact (assertion (state site s).1 (state site s).2 normal first second).2 (guards site s reached)
#print axioms assertion_family
end PV_B3P_PatternFamilies571227
