import NMT_R2_EmittedLength
import NMT_R2_Observation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_GetterEquality
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_Observation NMT_R2_EmittedData

theorem data_eq (keep : Bool) (a : Account) :
 NMT_R2_EmittedData.run keep a = cloned keep (account a).bytes := by
 unfold NMT_R2_EmittedData.run NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
 simp only [account]
 cases h : a.bytes with
 | Ok b => rfl
 | Err e =>
  change observe (fun b : Slice U8 => b.val.map byte)
   (do let pe ← clone keep e; .ok (.Err pe)) = cloned keep (.error (NMT_345.pe e))
  unfold clone cloned
  cases hc : (NMT_345.pe e).cloneAllocates <;> cases keep <;>
   simp only [hc,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true] <;> rfl

theorem length_eq (keep : Bool) (a : Account) :
 NMT_R2_EmittedLength.run keep a = cloned keep (account a).length := by
 unfold NMT_R2_EmittedLength.run
 simp only [account]
 cases h : a.length with
 | Ok n => rw [NMT_R2_EmittedLength.length_ok keep a n h]; rfl
 | Err e =>
  rw [NMT_R2_EmittedLength.length_error keep a e h]
  change observe (fun n : Usize => n.val)
   (mapOuter (mapCore id fromPE)
    (do let out ← mapOuter toPE (clone keep e); .ok (.Err out))) =
   cloned keep (.error (NMT_345.pe e))
  unfold clone cloned
  cases hc : (NMT_345.pe e).cloneAllocates <;> cases keep <;>
   simp only [hc,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true] <;>
   simp only [mapOuter,mapCore,bind_tc_ok,bind_tc_fail,from_toPE,observe,rustResult,silent,stopped]
#print axioms data_eq
#print axioms length_eq
end NMT_R2_GetterEquality
end
