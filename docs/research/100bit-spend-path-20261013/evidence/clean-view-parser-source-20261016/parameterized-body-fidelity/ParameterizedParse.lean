-- Mechanically extracted from pinned H generated Funs.lean.
-- Exact semantic adaptation: replace external query_checks calls with one
-- explicit function parameter; all other parse body tokens are retained.
import AspisR1ViewParseProbe.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1ViewParseProbe
noncomputable def verifier.View.parse_with_query_checks
  (query_checks : Slice Std.U8 → transport.Variant → Result (core.result.Result Unit verifier.Error))
  (bytes : Slice Std.U8) :
  Result (core.result.Result verifier.View verifier.Error)
  := do
  let r ← verifier.View.parse_shape bytes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    match val.folded_root_start with
    | none =>
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := val.semantic_start, «end» := val.semantic_end }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := val.y1_start, «end» := val.y1_end }
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := val.round0_start, «end» := val.round0_end }
      let s3 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := val.round1_start, «end» := val.round1_end }
      let s4 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start := val.final_start, «end» := val.final_end }
      let s5 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes
          { start := val.query_start }
      let r1 ← verifier.echeck s1 true
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← verifier.echeck s2 false
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let i ← transport.Variant.folds val.variant
          if i = 2#usize
          then
            let r3 ← verifier.echeck s3 false
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ← verifier.echeck s4 false
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r5 ← query_checks s5 val.variant
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  ok (core.result.Result.Ok
                    {
                      variant := val.variant,
                      semantic := s,
                      y1 := s1,
                      inactive := val.inactive,
                      round0 := s2,
                      folded_root := none,
                      round1 := s3,
                      final_message := s4,
                      query_bytes := s5
                    })
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    verifier.View (core.convert.FromSame verifier.Error)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  verifier.View (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                verifier.View (core.convert.FromSame verifier.Error) residual
          else
            let r3 ← verifier.echeck s4 false
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ← query_checks s5 val.variant
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                ok (core.result.Result.Ok
                  {
                    variant := val.variant,
                    semantic := s,
                    y1 := s1,
                    inactive := val.inactive,
                    round0 := s2,
                    folded_root := none,
                    round1 := s3,
                    final_message := s4,
                    query_bytes := s5
                  })
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  verifier.View (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                verifier.View (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.View (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.View (core.convert.FromSame verifier.Error) residual
    | some start =>
      let i ← start + 32#usize
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
          { start, «end» := i }
      let r1 ← core.array.TryFromSharedArraySlice.try_from 32#usize s
      let r2 ←
        core.result.Result.map_err
          verifier.View.parse.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError
          r1 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := val.semantic_start, «end» := val.semantic_end }
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := val.y1_start, «end» := val.y1_end }
        let s3 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := val.round0_start, «end» := val.round0_end }
        let s4 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := val.round1_start, «end» := val.round1_end }
        let s5 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := val.final_start, «end» := val.final_end }
        let s6 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) bytes
            { start := val.query_start }
        let r3 ← verifier.echeck s2 true
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r4 ← verifier.echeck s3 false
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let i1 ← transport.Variant.folds val.variant
            if i1 = 2#usize
            then
              let r5 ← verifier.echeck s4 false
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ← verifier.echeck s5 false
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r7 ← query_checks s6 val.variant
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    ok (core.result.Result.Ok
                      {
                        variant := val.variant,
                        semantic := s1,
                        y1 := s2,
                        inactive := val.inactive,
                        round0 := s3,
                        folded_root := (some val1),
                        round1 := s4,
                        final_message := s5,
                        query_bytes := s6
                      })
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      verifier.View (core.convert.FromSame verifier.Error)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    verifier.View (core.convert.FromSame verifier.Error)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  verifier.View (core.convert.FromSame verifier.Error) residual
            else
              let r5 ← verifier.echeck s5 false
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ← query_checks s6 val.variant
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  ok (core.result.Result.Ok
                    {
                      variant := val.variant,
                      semantic := s1,
                      y1 := s2,
                      inactive := val.inactive,
                      round0 := s3,
                      folded_root := (some val1),
                      round1 := s4,
                      final_message := s5,
                      query_bytes := s6
                    })
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    verifier.View (core.convert.FromSame verifier.Error)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  verifier.View (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              verifier.View (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.View (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.View (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.View (core.convert.FromSame verifier.Error) residual

end AspisR1ViewParseProbe
