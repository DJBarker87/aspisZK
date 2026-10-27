import RPu_FIr_GatherCallback
import RPu_FJn_WordRemainder
import RPu_FJk_CarrierRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_GatherCell
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K decode)
abbrev Claims := FIr_GatherCallback.Claims
def value (c : Claims) (n : Nat) : K :=
  match c.val[n/28]? with
  | none=>0
  | some row=>FIv_NativeArray.value row (n%28)
/-- The actual gather callback retains row-major width28 and source state. -/
theorem selected (c : Claims) (i : Usize) (out : field.QM31) (after : Claims)
    (run : FIr_GatherCallback.call c i=ok (out,after)) :
    decode out=value c i.val ∧ after=c := by
  unfold FIr_GatherCallback.call
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  obtain ⟨ri,hr,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨ci,hc,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨row,rr,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨q,rq,run⟩:=FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Result.ok.inj run)
  have rv:=FIx_WordArithmetic.div i 28#usize ri (by decide) hr
  change ri.val=i.val/28 at rv
  have cv:=FJn_WordRemainder.value i ci hc
  refine ⟨?_,rfl⟩
  unfold value
  rw [←rv,FIr_ArrayRead.slot c ri row rr]
  dsimp only
  rw [←cv,FIv_NativeArray.read row ci q rq]
#print axioms selected
end AspisR1.FJn_GatherCell
end
