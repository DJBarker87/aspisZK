import S6NativeSnapshotCodecV1
import S6NativeLateEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateChildDecode
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

@[step] theorem snapshot_spec (bytes : Slice U8) :
    decode_pair_live_snapshot_boxed_v1 bytes ⦃ result => ∀ value : PoolV1PairLiveSnapshotV1,
      result=core.result.Result.Ok value → decode_pool_v1_pair_live_snapshot_v1 bytes=ok (core.result.Result.Ok value) ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeSnapshotDecodeTotal.decode_total bytes
  apply exists_imp_spec
  cases result with
  | Ok value =>
    refine ⟨core.result.Result.Ok value,?_,?_⟩
    · simp [decode_pair_live_snapshot_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
      PoolV1PairLatePublicStatementErrorV1.SnapshotConstructor,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    · intro v eq; cases eq; exact run
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairLatePublicStatementErrorV1.Snapshot error),?_,?_⟩
    · simp [decode_pair_live_snapshot_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
      PoolV1PairLatePublicStatementErrorV1.SnapshotConstructor,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    · intro v eq; cases eq

@[step] theorem afterstate_spec (bytes : Slice U8) :
    decode_pair_afterstate_boxed_v1 bytes ⦃ result => ∀ value : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1,
      result=core.result.Result.Ok value → pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes=ok (core.result.Result.Ok value) ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeAfterstateCodec.decode_total bytes
  apply exists_imp_spec
  cases result with
  | Ok value =>
    refine ⟨core.result.Result.Ok value,?_,?_⟩
    · simp [decode_pair_afterstate_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
      PoolV1PairLatePublicStatementErrorV1.AfterstateConstructor,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    · intro v eq; cases eq; exact run
  | Err error =>
    refine ⟨core.result.Result.Err (PoolV1PairLatePublicStatementErrorV1.Afterstate error),?_,?_⟩
    · simp [decode_pair_afterstate_boxed_v1,run,core.result.Result.map_err,BuiltinFnOnce,
      PoolV1PairLatePublicStatementErrorV1.AfterstateConstructor,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
    · intro v eq; cases eq

@[step] theorem option_u64_eq_spec (a b : Option U64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 a b
      ⦃ result => result=decide (a=b) ⦄ := by
  apply exists_imp_spec
  cases a <;> cases b <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.cmp.PartialEqU64,liftFun2,read_discriminant,optionDiscriminantInst,optionDiscriminant]

#print axioms snapshot_spec
#print axioms afterstate_spec
#print axioms option_u64_eq_spec
end AspisS6NativeLateChildDecode
