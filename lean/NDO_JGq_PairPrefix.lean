import NDO_JGq_PairShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairPrefix
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE
def initial : Array E 7#usize := Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO

/-- Exact computation after the proved shape, power, allocation and shared
branch-selection prefix. Every remaining source call and error stays explicit. -/
def remaining : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
  let (r1, _, parts1) ←
    _root_.FIo_Native.weights.process_regular_kinds w true alpha f 2#usize 64#usize JGq_Powers0.a4
      JGq_Powers1.a4 scratch initial
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if true
    then
      let common := Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO
      let (self1, common1) ←
        _root_.FIo_Native.weights.Weights.pair_loop1
          { start := 0#usize, «end» := 16#usize } w common
      let r2 ← _root_.FIo_Native.weights.shared_partials f common1
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (r3, parts2) ← _root_.FIo_Native.weights.shared_high val self1 JGq_Powers0.a4 JGq_Powers1.a4 parts1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if 2#usize = 1#usize
          then
            let dual :=
              Array.repeat 16#usize
                FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
            let dual1 ←
              _root_.FIo_Native.weights.Weights.pair_loop2
                { start := 0#usize, «end» := 16#usize } JGq_Powers0.a4 dual
            let groups :=
              Array.repeat 16#usize
                FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
            let groups1 ←
              _root_.FIo_Native.weights.Weights.pair_loop3 { start := 0#usize, «end» := 64#usize }
                self1 f groups
            let parts3 ←
              _root_.FIo_Native.weights.Weights.pair_loop4
                { start := 1#usize, «end» := 16#usize } parts2 dual1
                groups1
            let parts4 ←
              _root_.FIo_Native.weights.Weights.pair_loop5
                { start := 0#usize, «end» := 2#usize } self1 f JGq_Powers0.a4 parts3
            let k ← _root_.FIo_Native.weights.powers 7#usize kappa
            let sum ←
              _root_.FIo_Native.weights.Weights.pair_loop6
                { start := 0#usize, «end» := 7#usize } parts4 k
                FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
            ok (core.result.Result.Ok sum)
          else
            let low :=
              Array.repeat 16#usize
                FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
            let low1 ←
              _root_.FIo_Native.weights.Weights.pair_loop7
                { start := 0#usize, «end» := 16#usize } JGq_Powers0.a4 JGq_Powers1.a4 low
            let we1 ← _root_.FIo_Native.weights.grouped_inactive_pair self1 f low1
            let a ← Array.update parts2 0#usize we1
            let b ←
              FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
                self1.variant FIo_Native.transport.Variant.S2
            let libra ←
              if b
              then _root_.FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 self1.extra
              else _root_.FIo_Native.weights.twofold_libra_weights low1 self1.extra
            let parts3 ←
              _root_.FIo_Native.weights.Weights.pair_loop8
                { start := 0#usize, «end» := 4#usize } f a libra
            let k ← _root_.FIo_Native.weights.powers 7#usize kappa
            let sum ←
              _root_.FIo_Native.weights.Weights.pair_loop9
                { start := 0#usize, «end» := 7#usize } parts3 k
                FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
            ok (core.result.Result.Ok sum)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            FIo_Native.aspis_core.field.wide_exact.WideExact (core.convert.FromSame
            FIo_Native.verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          FIo_Native.aspis_core.field.wide_exact.WideExact (core.convert.FromSame
          FIo_Native.verifier.Error) residual
    else
      if 2#usize = 1#usize
      then
        let dual :=
          Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
        let dual1 ←
          _root_.FIo_Native.weights.Weights.pair_loop10
            { start := 0#usize, «end» := 16#usize } JGq_Powers0.a4 dual
        let groups :=
          Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
        let groups1 ←
          _root_.FIo_Native.weights.Weights.pair_loop11 { start := 0#usize, «end» := 64#usize }
            w f groups
        let parts2 ←
          _root_.FIo_Native.weights.Weights.pair_loop12
            { start := 1#usize, «end» := 16#usize } parts1 dual1 groups1
        let parts3 ←
          _root_.FIo_Native.weights.Weights.pair_loop13
            { start := 0#usize, «end» := 2#usize } w f JGq_Powers0.a4 parts2
        let k ← _root_.FIo_Native.weights.powers 7#usize kappa
        let sum ←
          _root_.FIo_Native.weights.Weights.pair_loop14
            { start := 0#usize, «end» := 7#usize } parts3 k
            FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
        ok (core.result.Result.Ok sum)
      else
        let low :=
          Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
        let low1 ←
          _root_.FIo_Native.weights.Weights.pair_loop15
            { start := 0#usize, «end» := 16#usize } JGq_Powers0.a4 JGq_Powers1.a4 low
        let we1 ← _root_.FIo_Native.weights.grouped_inactive_pair w f low1
        let a ← Array.update parts1 0#usize we1
        let b ←
          FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant
            FIo_Native.transport.Variant.S2
        let libra ←
          if b
          then _root_.FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 w.extra
          else _root_.FIo_Native.weights.twofold_libra_weights low1 w.extra
        let parts2 ←
          _root_.FIo_Native.weights.Weights.pair_loop16
            { start := 0#usize, «end» := 4#usize } f a libra
        let k ← _root_.FIo_Native.weights.powers 7#usize kappa
        let sum ←
          _root_.FIo_Native.weights.Weights.pair_loop17
            { start := 0#usize, «end» := 7#usize } parts2 k
            FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
        ok (core.result.Result.Ok sum)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      FIo_Native.aspis_core.field.wide_exact.WideExact (core.convert.FromSame
      FIo_Native.verifier.Error) residual

/-- No successful Pair call or final gate is a premise. -/
theorem native : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
    w alpha f kappa=remaining := by
  unfold FIo_Native.weights.Weights.pair
  dsimp only
  rw [length,divided,bind_tc_ok,folds,expected,bind_tc_ok]
  have different : (64#usize != 64#usize)=false := by decide
  simp only [different,Bool.false_eq_true,ite_false,ite_true]
  rw [read0,bind_tc_ok,JGq_Powers0.source,bind_tc_ok,read1,bind_tc_ok,JGq_Powers1.source,bind_tc_ok,
    filled,bind_tc_ok]
  dsimp only
  have guard : FIo_Native.weights.shared_two_point_guard w 2#usize=ok true := by
    with_unfolding_all exact JGo_TX2_PairGuard.source
  rw [guard,bind_tc_ok]
  rfl
#print axioms native

def adapted : Result (core.result.Result AspisR1Stage2.Stage2Finish.E AspisR1Stage2.verifier.Error) := do
  let r ← remaining
  match r with
  | .Ok out=>ok (.Ok (FIo_Install.fromE out))
  | .Err e=>ok (.Err (FIo_Install.error e))

theorem source : FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
    (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=adapted := by
  have call : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))
      (FIo_Install.toWeights JGo_TX2_WeightData.value) (FIo_Install.toSlice JGo_TX2_FinishPrefix.alphas)
      (JFw_Frames.window 8007 2048) (FIo_Install.toE JFo_Prepared.value.kappa)=remaining := by
    with_unfolding_all exact native
  unfold FIo_Install.pair adapted
  rw [call]
  with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_PairPrefix
end
