import XRk_Funs
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRm_ResultCuts
theorem map_err_ok {T E E' F : Type} (fn : core.ops.function.FnOnce F E E')
    (r : core.result.Result T E) (c : F) (out : T)
    (run : core.result.Result.map_err fn r c=ok (.Ok out)) : r=.Ok out := by
  cases r with
  | Ok value =>
    have same := core.result.Result.Ok.inj (Result.ok.inj run)
    subst value
    rfl
  | Err e =>
    unfold core.result.Result.map_err at run
    obtain ⟨err,_,run⟩ := bind_success _ _ _ run
    cases run

theorem fibre (i v : Usize) (run : aspis_core.r0.domain.FibreIndex.new i=ok (.Ok v)) :
    v=i ∧ i<262144#usize := by
  unfold aspis_core.r0.domain.FibreIndex.new at run
  split at run
  · rename_i hi
    have same := core.result.Result.Ok.inj (Result.ok.inj run)
    exact ⟨same.symm,hi⟩
  · cases run
#print axioms map_err_ok
#print axioms fibre
end XRm_ResultCuts
