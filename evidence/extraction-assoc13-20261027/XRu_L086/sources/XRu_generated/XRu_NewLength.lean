import XRu_NewStep
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRu_NewLength
open XRu_NewStep
theorem loop (weights : Slice aspis_core.field.QM31) (raw out : Raw) (index : Usize)
 (inv : Inv weights (raw,index))
 (run : verifier.BatchedWeights.new_loop weights raw index=ok out) :
 out.val.length=weights.val.length := by
 unfold verifier.BatchedWeights.new_loop at run
 apply XRl_LoopInvariant.preserve _ (Inv weights)
  (fun out => out.val.length=weights.val.length) (measure weights)
  ?_ (raw,index) out inv run
 intro s r hi hr
 exact XRu_NewStep.source weights s r hi hr
/-- Pending rows are sized by THIS actual initialization and terms start at0.
The kit's unconditional allocation is not a native reservation certificate. -/
theorem source (weights : Slice aspis_core.field.QM31) (b : verifier.BatchedWeights)
 (run : verifier.BatchedWeights.new weights=ok (.Ok b)) :
 b.raw.val.length=weights.val.length ∧ b.terms=0#usize := by
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
  exact ⟨loop weights raw out 0#usize ⟨len,by simp [Inv]⟩ hloop,rfl⟩
#print axioms loop
#print axioms source
end XRu_NewLength
