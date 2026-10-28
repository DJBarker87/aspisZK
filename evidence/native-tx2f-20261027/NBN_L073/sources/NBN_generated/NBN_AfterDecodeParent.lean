import NBN_AfterDecode00
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecodeParent
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

def run (child : Decode) (bytes : Slice U8) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let i := Slice.len bytes
  let i1 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
  if i != i1
  then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength)
  else
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 4#usize }
    let s1 ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC { start := 0#usize, «end» := 4#usize }
    let b ← core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1
    if b
    then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic)
    else
      let i2 ← Slice.index_usize bytes 4#usize
      if i2 != pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
      then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion)
      else
        let i3 ← Slice.index_usize bytes 5#usize
        if i3 != pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
        then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat)
        else
          let i4 ← Slice.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding)
          else
            let i5 ← Slice.index_usize bytes 7#usize
            if i5 != 1#u8
            then ok (core.result.Result.Err pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode)
            else
              let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }
              let r ← pool_v1.pair_terminal.exact 32#usize s2
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r1 ← child val
                let r2 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  NBN_AfterDecode00.run child bytes val1
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (child : Decode) (lower : NBN_Dep_DigestDecode child) (bytes : Slice U8) :
    run child bytes = decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  have factored : run child bytes = AspisS6NativeAfterstateDecoderFactored.decode bytes := by
    have same : child = atomic_statement.decode_digest_canonical := funext lower
    unfold run
    simp only [NBN_AfterDecode00.source child lower]
    rw [same]
    unfold AspisS6NativeAfterstateDecoderFactored.decode
    run_tac do
      for _ in [:8] do
        let g ← Lean.Elab.Tactic.getMainGoal
        let t ← g.getType
        let names := t.getUsedConstants.filter fun n =>
          let s := n.toString
          (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
          (s.splitOn ".").any (fun c => c.startsWith "match_")
        if names.isEmpty then break
        let ids := names.map Lean.mkIdent
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
    dsimp only
    all_goals with_reducible rfl
  exact factored.trans (AspisS6NativeAfterstateDecoderFactored.decode_source bytes)

#print axioms source
end NBN_AfterDecodeParent
