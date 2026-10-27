import XSg_NewLoop
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSg_NewSource
open XSg_NewRows XRu_NewStep
/-- Complete raw-map and zero-counter provenance from the actual successful
constructor, on arbitrary source weights. Reservation is not inferred. -/
theorem source (weights : Slice Q) (b : verifier.BatchedWeights)
 (run : verifier.BatchedWeights.new weights=ok (.Ok b)) :
 b.raw.val=weights.val.map row ∧ b.terms=0#usize := by
 unfold verifier.BatchedWeights.new at run
 obtain ⟨r,hr,run⟩ := bind_success _ _ _ run
 cases r with
 | Err e =>
  simp [core.result.Result.map_err,
   verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
   core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from] at run
 | Ok raw =>
  have len := XRr_Initial64.filled _ (Slice.len weights) _ raw hr
  simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at run
  obtain ⟨out,hloop,run⟩ := bind_success _ _ _ run
  cases core.result.Result.Ok.inj (Result.ok.inj run)
  exact ⟨XSg_NewLoop.source weights raw out 0#usize ⟨len,by change 0≤weights.val.length;omega⟩
   (by intro j hj;change j<0 at hj;omega) hloop,rfl⟩
#print axioms source
end XSg_NewSource
