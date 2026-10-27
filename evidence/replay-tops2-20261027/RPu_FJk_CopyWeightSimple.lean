import RPu_FJk_CopyDescriptor
set_option autoImplicit false
namespace AspisR1.FJk_CopyWeightSimple
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

theorem discriminants :
    PoolV1PairForestCompiledVariantV1.PrivateTransfer.read_discriminant ≠
      PoolV1PairForestCompiledVariantV1.Withdrawal.read_discriminant := by
  change (0#isize : Isize) ≠ 1#isize
  intro h
  have hv := congrArg IScalar.val h
  have hz : (0#isize : Isize).val=0 := by scalar_tac
  have ho : (1#isize : Isize).val=1 := by scalar_tac
  rw [hz,ho] at hv
  omega

theorem zero (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=0#u8) (run : link_weight l index v=ok out) : out.val=1 := by
  unfold link_weight at run
  rw [hk] at run
  cases Result.ok.inj run
  simp only [field.M31.ONE,UScalar.ofNatCore_val_eq]

theorem transfer (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=1#u8) (run : link_weight l index v=ok out) :
    out.val=(match v with | .PrivateTransfer=>1 | .Withdrawal=>0) := by
  cases v <;>
    simp only [link_weight,hk,
      PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
      discriminants,Ne.symm discriminants,core.convert.num.FromU32Bool.from,
      lift,bind_tc_ok] at run
  all_goals cases Result.ok.inj run <;> simp [core.convert.num.FromU32Bool.from,discriminants,Ne.symm discriminants]

theorem withdrawal (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=2#u8) (run : link_weight l index v=ok out) :
    out.val=(match v with | .PrivateTransfer=>0 | .Withdrawal=>1) := by
  cases v <;>
    simp only [link_weight,hk,
      PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
      discriminants,Ne.symm discriminants,core.convert.num.FromU32Bool.from,
      lift,bind_tc_ok] at run
  all_goals cases Result.ok.inj run <;> simp [core.convert.num.FromU32Bool.from,discriminants,Ne.symm discriminants]
#print axioms discriminants
#print axioms zero
#print axioms transfer
#print axioms withdrawal
end AspisR1.FJk_CopyWeightSimple
