import NIG_CommonLoop
import NIG_LowLoop
import NIG_BothBranches
import NIG_LibraLoop
set_option autoImplicit false
noncomputable section
namespace NIG_PairModel
open Aeneas Aeneas.Std Result FIo_Native
variable [allocation:FIo_Native.Allocation]

theorem low_alias (ap0 ap1:NHX_LowDomain.Powers)
 (iter:core.ops.range.Range Usize) (cells:NHX_LowDomain.Cells):
 FIo_Native.weights.Weights.pair_loop7 iter ap0 ap1 cells=
 FIo_Native.weights.Weights.pair_loop15 iter ap0 ap1 cells:=
 NIG_BothBranches.low ap0 ap1 (iter,cells)

theorem final_alias (parts powers:NHX_FinalLoop.Cells)
 (iter:core.ops.range.Range Usize) (sum:FIo_Native.aspis_core.field.wide_exact.WideExact):
 FIo_Native.weights.Weights.pair_loop9 iter parts powers sum=
 FIo_Native.weights.Weights.pair_loop17 iter parts powers sum:=
 NIG_BothBranches.final parts powers (iter,sum)

def reference
  (self : _root_.FIo_Native.weights.Weights)
  (alpha : Slice aspis_core.field.wide_exact.WideExact) (f : Slice Std.U8)
  (kappa : aspis_core.field.wide_exact.WideExact) :
  Result (core.result.Result aspis_core.field.wide_exact.WideExact
    verifier.Error)
  := do
  let i := Slice.len f
  let n ← i / 32#usize
  let folds := Slice.len alpha
  let expected_n ←
    _root_.FIo_Native.weights.Weights.pair_loop0 { start := 0#usize, «end» := folds }
      1024#usize
  if n != expected_n
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let we ← Slice.index_usize alpha 0#usize
    let ap0 ← _root_.FIo_Native.weights.powers 4#usize we
    let ap1 ←
      if folds = 2#usize
      then
        do
        let we1 ← Slice.index_usize alpha 1#usize
        _root_.FIo_Native.weights.powers 4#usize we1
      else ok (Array.repeat 4#usize aspis_core.field.wide_exact.WideExact.ONE)
    let r ←
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy n
        aspis_core.field.QM31.ZERO
    match r with
    | core.result.Result.Ok v =>
      let parts :=
        Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO
      let shared_two_point ← _root_.FIo_Native.weights.shared_two_point_guard self folds
      let (r1, _, parts1) ←
        _root_.FIo_Native.weights.process_regular_kinds self shared_two_point alpha f folds n ap0
          ap1 v parts
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        if shared_two_point
        then
          let common := Array.repeat 16#usize aspis_core.field.QM31.ZERO
          let (self1, common1) ←
            NIG_CommonLoop.common_reference self common
          let r2 ← _root_.FIo_Native.weights.shared_partials f common1
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue val =>
            let (r3, parts2) ← _root_.FIo_Native.weights.shared_high val self1 ap0 ap1 parts1
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              if folds = 1#usize
              then
                let dual :=
                  Array.repeat 16#usize
                    aspis_core.field.wide_exact.WideExact.ZERO
                let dual1 ←
                  _root_.FIo_Native.weights.Weights.pair_loop2
                    { start := 0#usize, «end» := 16#usize } ap0 dual
                let groups :=
                  Array.repeat 16#usize
                    aspis_core.field.wide_exact.WideExact.ZERO
                let groups1 ←
                  _root_.FIo_Native.weights.Weights.pair_loop3 { start := 0#usize, «end» := n }
                    self1 f groups
                let parts3 ←
                  _root_.FIo_Native.weights.Weights.pair_loop4
                    { start := 1#usize, «end» := 16#usize } parts2 dual1
                    groups1
                let parts4 ←
                  _root_.FIo_Native.weights.Weights.pair_loop5
                    { start := 0#usize, «end» := 2#usize } self1 f ap0 parts3
                let k ← _root_.FIo_Native.weights.powers 7#usize kappa
                let sum ←
                  _root_.FIo_Native.weights.Weights.pair_loop6
                    { start := 0#usize, «end» := 7#usize } parts4 k
                    aspis_core.field.wide_exact.WideExact.ZERO
                ok (core.result.Result.Ok sum)
              else
                let low :=
                  Array.repeat 16#usize
                    aspis_core.field.wide_exact.WideExact.ZERO
                let low1 ←
                  NIG_LowLoop.low_reference ap0 ap1 low
                let we1 ← _root_.FIo_Native.weights.grouped_inactive_pair self1 f low1
                let a ← Array.update parts2 0#usize we1
                let b ←
                  transport.Variant.Insts.CoreCmpPartialEqVariant.eq
                    self1.variant transport.Variant.S2
                let libra ←
                  if b
                  then _root_.FIo_Native.weights.factored_s2_libra_weights ap0 ap1 self1.extra
                  else _root_.FIo_Native.weights.twofold_libra_weights low1 self1.extra
                let parts3 ←
                  NIG_LibraLoop.reference f libra a
                let k ← _root_.FIo_Native.weights.powers 7#usize kappa
                let sum ←
                  NHX_FinalLoop.reference parts3 k
                ok (core.result.Result.Ok sum)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                aspis_core.field.wide_exact.WideExact (core.convert.FromSame
                verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.field.wide_exact.WideExact (core.convert.FromSame
              verifier.Error) residual
        else
          if folds = 1#usize
          then
            let dual :=
              Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO
            let dual1 ←
              _root_.FIo_Native.weights.Weights.pair_loop10
                { start := 0#usize, «end» := 16#usize } ap0 dual
            let groups :=
              Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO
            let groups1 ←
              _root_.FIo_Native.weights.Weights.pair_loop11 { start := 0#usize, «end» := n }
                self f groups
            let parts2 ←
              _root_.FIo_Native.weights.Weights.pair_loop12
                { start := 1#usize, «end» := 16#usize } parts1 dual1 groups1
            let parts3 ←
              _root_.FIo_Native.weights.Weights.pair_loop13
                { start := 0#usize, «end» := 2#usize } self f ap0 parts2
            let k ← _root_.FIo_Native.weights.powers 7#usize kappa
            let sum ←
              _root_.FIo_Native.weights.Weights.pair_loop14
                { start := 0#usize, «end» := 7#usize } parts3 k
                aspis_core.field.wide_exact.WideExact.ZERO
            ok (core.result.Result.Ok sum)
          else
            let low :=
              Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO
            let low1 ←
              NIG_LowLoop.low_reference ap0 ap1 low
            let we1 ← _root_.FIo_Native.weights.grouped_inactive_pair self f low1
            let a ← Array.update parts1 0#usize we1
            let b ←
              transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
                transport.Variant.S2
            let libra ←
              if b
              then _root_.FIo_Native.weights.factored_s2_libra_weights ap0 ap1 self.extra
              else _root_.FIo_Native.weights.twofold_libra_weights low1 self.extra
            let parts2 ←
              NIG_LibraLoop.reference f libra a
            let k ← _root_.FIo_Native.weights.powers 7#usize kappa
            let sum ←
              NHX_FinalLoop.reference parts2 k
            ok (core.result.Result.Ok sum)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.wide_exact.WideExact (core.convert.FromSame
          verifier.Error) residual
    | core.result.Result.Err _ =>
      ok (core.result.Result.Err verifier.Error.Allocation)

theorem source (w:FIo_Native.weights.Weights)
 (alpha:Slice aspis_core.field.wide_exact.WideExact) (f:Slice U8)
 (kappa:aspis_core.field.wide_exact.WideExact):
 FIo_Native.weights.Weights.pair w alpha f kappa=reference w alpha f kappa:=by
 unfold FIo_Native.weights.Weights.pair reference
 simp only [low_alias,NIG_BothBranches.libra,final_alias,
  NIG_CommonLoop.common_source,NIG_LowLoop.low_source,NIG_LibraLoop.source,NHX_FinalLoop.source]
 rfl
#print axioms low_alias
#print axioms final_alias
#print axioms source
end NIG_PairModel
