import NIG_PairModel
import NIG_PairGeometry
set_option autoImplicit false
noncomputable section
namespace NIG_PairS2Body
open Aeneas Aeneas.Std Result FIo_Native AspisR1
variable [FIo_Native.Allocation]

def reference (self:weights.Weights) (alpha:Slice aspis_core.field.wide_exact.WideExact)
 (f:Slice U8) (kappa:aspis_core.field.wide_exact.WideExact):
 Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error):=do
    let we ← Slice.index_usize alpha 0#usize
    let ap0 ← _root_.FIo_Native.weights.powers 4#usize we
    let we1 ← Slice.index_usize alpha 1#usize
    let ap1 ← _root_.FIo_Native.weights.powers 4#usize we1
    let r ←
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy 64#usize
        aspis_core.field.QM31.ZERO
    match r with
    | core.result.Result.Ok v =>
      let parts :=
        Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO
      let shared_two_point ← _root_.FIo_Native.weights.shared_two_point_guard self 2#usize
      let (r1, _, parts1) ←
        _root_.FIo_Native.weights.process_regular_kinds self shared_two_point alpha f 2#usize 64#usize ap0
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

theorem source (w:weights.Weights) (p:AspisR1Stage2.verifier.Prepared) (f:Slice U8)
 (width:f.val.length=2048) (kappa:aspis_core.field.wide_exact.WideExact):
 weights.Weights.pair w (FIo_Install.toSlice p.alpha.to_slice) f kappa=
 reference w (FIo_Install.toSlice p.alpha.to_slice) f kappa:=by
 rw [NIG_PairModel.source]
 unfold NIG_PairModel.reference reference
 dsimp only
 rw [NIG_PairGeometry.message_cells f width]
 simp only [bind_tc_ok,NIG_PairGeometry.alpha_length,NIG_Geometry.expected]
 rfl
#print axioms source
end NIG_PairS2Body
