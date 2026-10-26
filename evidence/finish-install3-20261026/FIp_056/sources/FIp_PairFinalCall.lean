import FIo_Install
import FIp_FinalSumAliases
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PairFinalCall
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

/-- Every successful native Pair reaches its own seven-part final sum and
powers call. The arrays are taken from that run, including one-fold paths. -/
theorem reached [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (parts k : Array NE 7#usize),
      FIo_Native.weights.powers 7#usize kappa=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out := by
  unfold FIo_Native.weights.Weights.pair at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals exact ⟨_,_,by assumption,by assumption⟩

#print axioms reached
end AspisR1.FIp_PairFinalCall
end
