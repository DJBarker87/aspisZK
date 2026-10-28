import NDO_JGs_Regular
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairShared0
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE
def shared (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
  let common := Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO
  let (self1, common1) ←
    _root_.FIo_Native.weights.Weights.pair_loop1
      { start := 0#usize, «end» := 16#usize } w common
  let r2 ← _root_.FIo_Native.weights.shared_partials f common1
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r3, parts2) ← _root_.FIo_Native.weights.shared_high val self1 JGq_Powers0.a4 JGq_Powers1.a4 parts
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
theorem source : JGq_PairPrefix.remaining=shared JGs_K4.parts := by
  unfold JGq_PairPrefix.remaining shared
  rw [JGs_Regular.source,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,ite_true]
  rfl
#print axioms source
end AspisR1.JGv_PairShared0
end
