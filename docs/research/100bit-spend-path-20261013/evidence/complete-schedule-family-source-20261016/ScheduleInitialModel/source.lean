import ScheduleDomainToModel
import AbsorptionSelectorSetup

/-! Generic identities between the source-program component models and the
retained schedule relation. These do not expand any selector sum or field. -/
set_option autoImplicit false
namespace AspisR1.ScheduleInitialModel
open AspisR1.ScheduleDomainToModel
variable {K : Type} [Field K]
attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh R0P.scheduleNodes

def baseValue (p : Registers K) (z : Fin 16 → K) (i : Fin 16) : K :=
  (if i.val < 8 then p.full + p.rate else p.full) * z i

def initialValue (p : Registers K) (z : Fin 16 → K) (i : Fin 16) : K :=
  if i.val = 8 then baseValue p z i - p.low0 * domainModel p
  else if i.val = 9 then baseValue p z i - p.low0 * lengthModel p
  else baseValue p z i

theorem initialValue_eq_schedule (v : R0P.Variant) (o : R0P.Openings K)
    (sel : R0P.Sel K) (i : Fin 16) :
    initialValue (AspisR1.InitialSelectorPrefix.model v sel) o.z i = R0P.scheduleInitial v o sel i := by
  have h8 : i = (8 : Fin 16) ↔ i.val = 8 := by
    constructor
    · intro h; subst i; rfl
    · intro h; apply Fin.ext; exact h
  have h9 : i = (9 : Fin 16) ↔ i.val = 9 := by
    constructor
    · intro h; subst i; rfl
    · intro h; apply Fin.ext; exact h
  cases v <;>
    dsimp only [initialValue, baseValue, domainModel, lengthModel,
      AspisR1.InitialSelectorPrefix.model, R0P.scheduleInitial, R0P.scheduleVariantSelectors] <;>
    simp only [h8, h9, ite_mul]

theorem absorptionValue_eq_schedule (v : R0P.Variant) (o : R0P.Openings K)
    (sel : R0P.Sel K) (i : Fin 16) :
    let p := AspisR1.AbsorptionSelectorSetup.model v sel
    R0P.scheduleAbsorptionLiteral p.low p.fixed p.two p.eight p.nodes o.z i =
      R0P.scheduleAbsorption v o sel i := by
  cases v <;>
    dsimp only [AspisR1.AbsorptionSelectorSetup.model, AspisR1.InitialSelectorPrefix.model,
      R0P.scheduleAbsorption, R0P.scheduleVariantSelectors]

#print axioms initialValue_eq_schedule
#print axioms absorptionValue_eq_schedule
end AspisR1.ScheduleInitialModel
