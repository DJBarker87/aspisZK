import NGX_RecordAt
import NGX_PrefixGeometry
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser
namespace AspisR1.NGX_PrefixSource
def computation (parseAt : Slice U8→U8→Usize→Result (core.result.Result (Slice U8×Usize) r1_wire.Error))
  (bytes : Slice Std.U8) :
  Result (core.result.Result r1_wire.Prefix r1_wire.Error)
  := do
  let i := Slice.len bytes
  if i < 32#usize
  then ok (core.result.Result.Err (r1_wire.Error.Length 0#u8))
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 32#usize }
    let r ← core.array.TryFromSharedArraySlice.try_from 32#usize s
    match r with
    | core.result.Result.Ok root =>
      let r1 ← parseAt bytes 0#u8 32#usize
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue p =>
        let (r0, offset) := p
        let r2 ← parseAt bytes 1#u8 offset
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue p1 =>
          let (r11, offset1) := p1
          let r3 ← parseAt bytes 2#u8 offset1
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue p2 =>
            let (r21, offset2) := p2
            let r4 ← parseAt bytes 3#u8 offset2
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue p3 =>
              let (r31, offset3) := p3
              let r5 ← parseAt bytes 4#u8 offset3
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue p4 =>
                let (r41, offset4) := p4
                let r6 ← parseAt bytes 5#u8 offset4
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue p5 =>
                  let (r51, offset5) := p5
                  let r7 ← parseAt bytes 6#u8 offset5
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue p6 =>
                    let (r61, offset6) := p6
                    let r8 ← parseAt bytes 7#u8 offset6
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue p7 =>
                      let (r71, offset7) := p7
                      let r9 ← parseAt bytes 8#u8 offset7
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue p8 =>
                        let (r81, offset8) := p8
                        let r10 ← parseAt bytes 9#u8 offset8
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r10
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue p9 =>
                          let (r91, offset9) := p9
                          let r12 ←
                            parseAt bytes 10#u8 offset9
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue p10 =>
                            let (r101, offset10) := p10
                            let r13 ←
                              parseAt bytes 11#u8 offset10
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue p11 =>
                              let (r111, offset11) := p11
                              let r14 ←
                                parseAt bytes 12#u8 offset11
                              let cf12 ←
                                core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf12 with
                              | core.ops.control_flow.ControlFlow.Continue p12
                                =>
                                let (r121, offset12) := p12
                                let r15 ←
                                  parseAt bytes 13#u8 offset12
                                let cf13 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf13 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  p13 =>
                                  let (r131, offset13) := p13
                                  let r16 ←
                                    parseAt bytes 14#u8
                                      offset13
                                  let cf14 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf14 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    p14 =>
                                    let (r141, offset14) := p14
                                    let r17 ←
                                      parseAt bytes 15#u8
                                        offset14
                                    let cf15 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf15 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      p15 =>
                                      let (r151, offset15) := p15
                                      let r18 ←
                                        parseAt bytes 16#u8
                                          offset15
                                      let cf16 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf16 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        p16 =>
                                        let (r161, offset16) := p16
                                        let r19 ←
                                          parseAt bytes 17#u8
                                            offset16
                                        let cf17 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf17 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          p17 =>
                                          let (r171, offset17) := p17
                                          let r20 ←
                                            parseAt bytes 18#u8
                                              offset17
                                          let cf18 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf18 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            p18 =>
                                            let (r181, offset18) := p18
                                            let r22 ←
                                              parseAt bytes
                                                19#u8 offset18
                                            let cf19 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r22
                                            match cf19 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              p19 =>
                                              let (r191, offset19) := p19
                                              let r23 ←
                                                parseAt bytes
                                                  20#u8 offset19
                                              let cf20 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r23
                                              match cf20 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                p20 =>
                                                let (r201, offset20) := p20
                                                let r24 ←
                                                  parseAt bytes
                                                    21#u8 offset20
                                                let cf21 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r24
                                                match cf21 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  p21 =>
                                                  let (r211, offset21) := p21
                                                  let r25 ←
                                                    parseAt
                                                      bytes 22#u8 offset21
                                                  let cf22 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r25
                                                  match cf22 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    p22 =>
                                                    let (r221, offset22) := p22
                                                    let r26 ←
                                                      parseAt
                                                        bytes 23#u8 offset22
                                                    let cf23 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r26
                                                    match cf23 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      p23 =>
                                                      let (r231, offset23) :=
                                                        p23
                                                      let r27 ←
                                                        parseAt
                                                          bytes 24#u8 offset23
                                                      let cf24 ←
                                                        core.result.Result.Insts.CoreOpsTry.branch
                                                          r27
                                                      match cf24 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        p24 =>
                                                        let (r241, offset24) :=
                                                          p24
                                                        let r28 ←
                                                          parseAt
                                                            bytes 25#u8
                                                            offset24
                                                        let cf25 ←
                                                          core.result.Result.Insts.CoreOpsTry.branch
                                                            r28
                                                        match cf25 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          p25 =>
                                                          let (r251, offset25)
                                                            :=
                                                            p25
                                                          let r29 ←
                                                            parseAt
                                                              bytes 26#u8
                                                              offset25
                                                          let cf26 ←
                                                            core.result.Result.Insts.CoreOpsTry.branch
                                                              r29
                                                          match cf26 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            p26 =>
                                                            let (r261,
                                                              offset26) :=
                                                              p26
                                                            let i1 :=
                                                              Slice.len bytes
                                                            if offset26 != i1
                                                            then
                                                              ok
                                                                (core.result.Result.Err
                                                                r1_wire.Error.TrailingBytes)
                                                            else
                                                              ok
                                                                (core.result.Result.Ok
                                                                {
                                                                  c1_root :=
                                                                    root,
                                                                  records :=
                                                                    (Array.make
                                                                    27#usize [
                                                                    r0, r11,
                                                                    r21, r31,
                                                                    r41, r51,
                                                                    r61, r71,
                                                                    r81, r91,
                                                                    r101, r111,
                                                                    r121, r131,
                                                                    r141, r151,
                                                                    r161, r171,
                                                                    r181, r191,
                                                                    r201, r211,
                                                                    r221, r231,
                                                                    r241, r251,
                                                                    r261
                                                                    ])
                                                                })
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                              r1_wire.Prefix
                                                              (core.convert.FromSame
                                                              r1_wire.Error)
                                                              residual
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                            r1_wire.Prefix
                                                            (core.convert.FromSame
                                                            r1_wire.Error)
                                                            residual
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                          r1_wire.Prefix
                                                          (core.convert.FromSame
                                                          r1_wire.Error)
                                                          residual
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        r1_wire.Prefix
                                                        (core.convert.FromSame
                                                        r1_wire.Error) residual
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      r1_wire.Prefix
                                                      (core.convert.FromSame
                                                      r1_wire.Error) residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    r1_wire.Prefix
                                                    (core.convert.FromSame
                                                    r1_wire.Error) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  r1_wire.Prefix
                                                  (core.convert.FromSame
                                                  r1_wire.Error) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                r1_wire.Prefix
                                                (core.convert.FromSame
                                                r1_wire.Error) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              r1_wire.Prefix
                                              (core.convert.FromSame
                                              r1_wire.Error) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            r1_wire.Prefix
                                            (core.convert.FromSame
                                            r1_wire.Error) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          r1_wire.Prefix (core.convert.FromSame
                                          r1_wire.Error) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        r1_wire.Prefix (core.convert.FromSame
                                        r1_wire.Error) residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      r1_wire.Prefix (core.convert.FromSame
                                      r1_wire.Error) residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    r1_wire.Prefix (core.convert.FromSame
                                    r1_wire.Error) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  r1_wire.Prefix (core.convert.FromSame
                                  r1_wire.Error) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                r1_wire.Prefix (core.convert.FromSame
                                r1_wire.Error) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              r1_wire.Prefix (core.convert.FromSame
                              r1_wire.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            r1_wire.Prefix (core.convert.FromSame
                            r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
    | core.result.Result.Err _ =>
      ok (core.result.Result.Err (r1_wire.Error.Length 0#u8))


theorem source (bytes : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
 computation AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes := by rfl
#print axioms source
end AspisR1.NGX_PrefixSource
