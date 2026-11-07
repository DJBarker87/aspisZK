import NNG_ConcreteCalls136
import NNG_LIBEvents136
import NNG_EnvCallGraph136
import LIB_Mark
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteMark136
open Aeneas Aeneas.Std Result NNG_Emitted

theorem source (env : RSL.Env) (rawObs : Observer)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (i : U8) :
    (NNG_ConcreteCalls136.calls env).c9 rawObs i = AspisR1PublicPreparation.VerifyPrefix.mark obs i := by
  rw [LIB_Mark.result]
  rfl
#print axioms source

theorem mark2 (env : RSL.Env) (obs : Observer) :
    RSL.Spec.map id (NNG_Interpret136.call NNG_LIBEvents136.events "mark2" (obs,2#u8)
      ((NNG_ConcreteCalls136.calls env).c9 obs 2#u8)) env = (RSL.Spec.pure ()) env := by
  exact NNG_EnvCallGraph136.pure_at id NNG_LIBEvents136.events "mark2" (obs,2#u8) _ env () () rfl rfl
    (NNG_LIBEvents136.silent env "mark2" _ _ (by decide) (by decide) (by decide))
#print axioms mark2

theorem mark3 (env : RSL.Env) (obs : Observer) :
    RSL.Spec.map id (NNG_Interpret136.call NNG_LIBEvents136.events "mark3" (obs,3#u8)
      ((NNG_ConcreteCalls136.calls env).c9 obs 3#u8)) env = (RSL.Spec.pure ()) env := by
  exact NNG_EnvCallGraph136.pure_at id NNG_LIBEvents136.events "mark3" (obs,3#u8) _ env () () rfl rfl
    (NNG_LIBEvents136.silent env "mark3" _ _ (by decide) (by decide) (by decide))
#print axioms mark3

theorem mark4 (env : RSL.Env) (obs : Observer) :
    RSL.Spec.map id (NNG_Interpret136.call NNG_LIBEvents136.events "mark4" (obs,4#u8)
      ((NNG_ConcreteCalls136.calls env).c9 obs 4#u8)) env = (RSL.Spec.pure ()) env := by
  exact NNG_EnvCallGraph136.pure_at id NNG_LIBEvents136.events "mark4" (obs,4#u8) _ env () () rfl rfl
    (NNG_LIBEvents136.silent env "mark4" _ _ (by decide) (by decide) (by decide))
#print axioms mark4

theorem mark5 (env : RSL.Env) (obs : Observer) :
    RSL.Spec.map id (NNG_Interpret136.call NNG_LIBEvents136.events "mark5" (obs,5#u8)
      ((NNG_ConcreteCalls136.calls env).c9 obs 5#u8)) env = (RSL.Spec.pure ()) env := by
  exact NNG_EnvCallGraph136.pure_at id NNG_LIBEvents136.events "mark5" (obs,5#u8) _ env () () rfl rfl
    (NNG_LIBEvents136.silent env "mark5" _ _ (by decide) (by decide) (by decide))
#print axioms mark5
end AspisR1.NNG_ConcreteMark136
