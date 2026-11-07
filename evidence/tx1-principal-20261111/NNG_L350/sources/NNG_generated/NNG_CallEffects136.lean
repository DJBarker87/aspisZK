import NNG_FinalEvents136
import NNG_ConcreteMark136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CallEffects136
open Aeneas Aeneas.Std Result NNG_Emitted NNG_EmittedCallGraph NNG_Observed136

theorem congr {Args A B : Type} (decode : A→B) (site : String) (args : Args) (r : Result A) (env : RSL.Env)
    (e1 e2 : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (same : e1 env (.call site args r)=e2 env (.call site args r)) :
    RSL.Spec.map decode (NNG_Interpret136.call e1 site args r) env =
      RSL.Spec.map decode (NNG_Interpret136.call e2 site args r) env := by
  rw [call_projection,call_projection]
  funext out
  change (out=⟨exit decode r,e1 env (.call site args r)⟩) = (out=⟨exit decode r,e2 env (.call site args r)⟩)
  rw [same]
#print axioms congr

theorem nonUnit {Args A B : Type} (decode : A→B) (site : String) (args : Args) (r : Result A) (env : RSL.Env)
    (different : A≠Unit) :
    RSL.Spec.map decode (NNG_Interpret136.call NNG_FinalEvents136.events site args r) env =
      RSL.Spec.map decode (NNG_Interpret136.call NNG_LIBEvents136.events site args r) env :=
  congr decode site args r env _ _ (NNG_FinalEvents136.nonUnit env site args r different)
#print axioms nonUnit

theorem mark (env : RSL.Env) (site : String) (obs : Observer) (i : U8) :
    RSL.Spec.map id (NNG_Interpret136.call NNG_FinalEvents136.events site (obs,i)
      ((NNG_ConcreteCalls136.calls env).c9 obs i)) env = (RSL.Spec.pure ()) env := by
  exact NNG_EnvCallGraph136.pure_at id NNG_FinalEvents136.events site (obs,i) _ env () () rfl rfl
    (NNG_FinalEvents136.unit env site (obs,i) _)
#print axioms mark
end AspisR1.NNG_CallEffects136
