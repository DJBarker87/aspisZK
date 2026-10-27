import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRw21FixCongruence
/-- Equal step functionals have equal least fixed points. This is symbolic;
no iteration count or concrete recursive state is normalized. -/
theorem function {α : Type} [Lean.Order.CCPO α] (f g : α → α)
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) (same : f=g) :
    Lean.Order.fix f hf=Lean.Order.fix g hg := by
  subst g
  rfl
#print axioms function
end R1Z.ProverRw21FixCongruence
