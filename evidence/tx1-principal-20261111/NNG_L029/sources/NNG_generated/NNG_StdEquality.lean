import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_StdEquality
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
-- Rust derives PartialEq/Eq componentwise on these exact record carriers.
deriving instance DecidableEq for aspis_core.field.CM31
deriving instance DecidableEq for aspis_core.field.QM31
deriving instance DecidableEq for aspis_core.circle.SecureCirclePoint

def qeq (x y : Q) : Result Bool := .ok (decide (x=y))
def pointEq (x y : aspis_core.circle.SecureCirclePoint) : Result Bool := .ok (decide (x=y))
/-- Expanding the trait-default ne in the compilation interface preserves
exactly that default; no result or semantic hypothesis is introduced. -/
theorem ne_default (eq : Q → Q → Result Bool) (x y : Q) :
 core.cmp.PartialEq.ne.trait_default (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 eq) x y=
 (do let b ← eq x y; .ok (!b)) := rfl
/-- The first explicit guard is the precise inequality in frozen RowSpec136. -/
theorem terminal_guard (x y : Q) :
 core.cmp.PartialEq.ne.trait_default (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 qeq) x y=
 .ok (decide (x≠y)) := by
 rw [ne_default]
 by_cases h : x=y <;> simp [qeq,h]
/-- The second explicit guard is the precise equality in frozen RowSpec136. -/
theorem circle_guard (x y : aspis_core.circle.SecureCirclePoint) :
 pointEq x y=.ok (decide (x=y)) := rfl
#print axioms ne_default
#print axioms terminal_guard
#print axioms circle_guard
end AspisR1.NNG_StdEquality
