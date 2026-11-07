import NNG_EnvCallGraph136
import LIB_Carriers
set_option autoImplicit false
namespace AspisR1.NNG_ConcreteGraph136
open Aeneas Aeneas.Std Result NNG_Observed136 NNG_EmittedCallGraph

theorem resultObs {A B : Type} (decode : A → B) (r : Result A) (target : Result B)
    (events : List RSL.Event) (mapped : resultMap decode r = target) :
    (⟨exit decode r,events⟩ : RSL.Obs B) = LIB_Carriers.resultObs id events target := by
  rw [←mapped]
  cases r <;> rfl
#print axioms resultObs
theorem mappedObs {A B : Type} (decode : A → B) (r : Result A) (events : List RSL.Event) :
    LIB_Carriers.resultObs decode events r = LIB_Carriers.resultObs id events (resultMap decode r) := by
  cases r <;> rfl
#print axioms mappedObs
end AspisR1.NNG_ConcreteGraph136
