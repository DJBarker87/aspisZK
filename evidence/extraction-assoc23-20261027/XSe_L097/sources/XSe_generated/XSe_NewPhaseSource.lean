import XSe_NewPhase
import XRu_NewLength
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_NewPhaseSource
open XRu_NewStep XSe_InitialRowPhase
/-- Initial pending phase is derived from the actual constructor, on arbitrary
input weights. This does not assert periodic-phase preservation by queries. -/
theorem source (weights : Slice aspis_core.field.QM31) (b : verifier.BatchedWeights)
 (run : verifier.BatchedWeights.new weights=ok (.Ok b)) : Small b.raw ∧ b.terms=0#usize := by
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
   have initial : Small raw := by
    unfold aspis_core.r0.heap.filled at hr
    rw [dif_pos (by scalar_tac)] at hr
    have same := core.result.Result.Ok.inj (Result.ok.inj hr)
    rw [←same]
    intro row member
    simp only [List.mem_replicate] at member
    rcases member with ⟨_,rfl⟩
    intro word hw
    simp only [Array.repeat,List.mem_replicate] at hw
    rcases hw with ⟨_,rfl⟩
    decide
   simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at run
   obtain ⟨out,hloop,run⟩ := bind_success _ _ _ run
   cases core.result.Result.Ok.inj (Result.ok.inj run)
   exact ⟨XSe_NewPhase.loop weights raw out 0#usize
    ⟨len,by change 0≤weights.val.length;omega⟩ initial hloop,rfl⟩
#print axioms source
end XSe_NewPhaseSource
