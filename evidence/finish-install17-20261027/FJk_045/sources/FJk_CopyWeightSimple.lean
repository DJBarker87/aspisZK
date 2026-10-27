import FJk_CopyDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_CopyWeightSimple
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

theorem zero (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=0#u8) (run : link_weight l index v=ok out) : out.val=1 := by
  unfold link_weight at run
  rw [hk] at run
  cases Result.ok.inj run
  rfl

theorem transfer (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=1#u8) (run : link_weight l index v=ok out) :
    out.val=(match v with | .PrivateTransfer=>1 | .Withdrawal=>0) := by
  cases v <;>
    simp only [link_weight,hk,
      PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
      lift,bind_tc_ok] at run
  all_goals cases Result.ok.inj run <;> rfl

theorem withdrawal (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=2#u8) (run : link_weight l index v=ok out) :
    out.val=(match v with | .PrivateTransfer=>0 | .Withdrawal=>1) := by
  cases v <;>
    simp only [link_weight,hk,
      PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
      lift,bind_tc_ok] at run
  all_goals cases Result.ok.inj run <;> rfl
#print axioms zero
#print axioms transfer
#print axioms withdrawal
end AspisR1.FJk_CopyWeightSimple
