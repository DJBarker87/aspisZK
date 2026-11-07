import NNG_EmittedContext
set_option autoImplicit false
namespace AspisR1.NNG_Equality136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
-- The standard equality interpretation is componentwise on these records.
deriving instance DecidableEq for aspis_core.field.CM31
deriving instance DecidableEq for aspis_core.field.QM31
deriving instance DecidableEq for aspis_core.circle.SecureCirclePoint

def qeq (x y : Q) : Result Bool := .ok (decide (x=y))
def pointEq (x y : aspis_core.circle.SecureCirclePoint) : Result Bool := .ok (decide (x=y))

/-- Direct pure instantiation of the trait default; no arbitrary Result
projection is split before the generated trait has been reduced. -/
theorem terminal_guard (x y : Q) :
    core.cmp.PartialEq.ne.trait_default
      (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 qeq) x y = .ok (decide (x≠y)) := by
  change (do let b ← qeq x y; ok (decide (¬b = true))) = .ok (decide (x≠y))
  by_cases h : x=y <;> simp [qeq,h]
#print axioms terminal_guard

theorem circle_guard (x y : aspis_core.circle.SecureCirclePoint) :
    pointEq x y = .ok (decide (x=y)) := rfl
#print axioms circle_guard
end AspisR1.NNG_Equality136
