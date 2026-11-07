import RSL_Base
set_option autoImplicit false
namespace LIBB_ReturnFunctional
/-- At a fixed environment there is at most one returned observation,
including its value and ordered events. Abort/divergence arms are unrestricted. -/
def ReturnFunctional {α : Type} (m : RSL.Spec α) : Prop :=
 ∀ env o₁ o₂ r₁ r₂, m env o₁ → m env o₂ →
 o₁.exit = .ret r₁ → o₂.exit = .ret r₂ → o₁ = o₂
end LIBB_ReturnFunctional
