import FJc_SharedSelf
import FJc_LowValue
import FJc_LibraFrame
import FIp_FinalSumAliases
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_PairInactiveTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
attribute [local irreducible] FIo_Native.weights.powers
  FIo_Native.weights.Weights.pair_loop15 FIo_Native.weights.grouped_inactive_pair
  FIo_Native.weights.Weights.pair_loop16 FIo_Native.weights.Weights.pair_loop17
/-- Joint original Pair trace: the inactive value, its write to part0,
Libra-only continuation and final sum all belong to ONE producing call. -/
theorem reached [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize) (inactive : NE)
      (before after parts k : Array NE 7#usize) (libra : Array NE 4#usize),
      Slice.index_usize alpha 0#usize=ok a0 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧
      Slice.index_usize alpha 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low ∧
      FIo_Native.weights.grouped_inactive_pair self f low=ok inactive ∧
      Array.update before 0#usize inactive=ok after ∧
      FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f after libra=ok parts ∧
      FIo_Native.weights.powers 7#usize kappa=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out := by
  unfold FIo_Native.weights.Weights.pair at run
  simp only [folds,ite_true,show ¬(2#usize=1#usize) from by decide,ite_false] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    obtain ⟨a1,h1,hp1⟩ := Port3_PushFrame.bind_success
      (Slice.index_usize alpha 1#usize) (fun a=>FIo_Native.weights.powers 4#usize a) _ (by assumption)
    try
      have same := FJc_SharedSelf.value self _ _ _ _ (by assumption)
      subst_vars
    try simp only [FJc_LowValue.seven_alias,FJc_LibraFrame.eight_alias,FIp_FinalSumAliases.nine] at *
    have same := core.result.Result.Ok.inj (Result.ok.inj run)
    cases same
    exact ⟨_,a1,_,_,_,_,_,_,_,_,_,by assumption,by assumption,h1,hp1,
      by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩
#print axioms reached
end AspisR1.FJc_PairInactiveTrace
end
