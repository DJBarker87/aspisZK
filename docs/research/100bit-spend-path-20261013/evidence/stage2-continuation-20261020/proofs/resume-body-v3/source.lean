import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1Stage2
structure ResumeOps where
  checkpointSize : transport.Variant → Result Usize
  tag : transport.Variant → Result U8
  finalLen : transport.Variant → Result Usize
  eq : {T U : Type} → {N : Usize} → core.cmp.PartialEq T U → Slice T → Array U N → Result Bool
  ne : {T U : Type} → {N : Usize} → core.cmp.PartialEq T U → Slice T → Array U N → Result Bool
  headerAny : core.slice.iter.Iter U8 → Result (Bool × core.slice.iter.Iter U8)
  raw : (N : Usize) → verifier.Reader → Result (Array U8 N × verifier.Reader)
  readE : verifier.Reader → Result (core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error × verifier.Reader)
  readK : verifier.Reader → Result (core.result.Result aspis_core.field.QM31 verifier.Error × verifier.Reader)
  validate : Array U32 22#usize → Result (core.result.Result Unit verifier.Error)
  zeroK : Result aspis_core.field.QM31
  filled : Usize → aspis_core.field.QM31 → Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error)
  readQueries : Slice U8 → Usize → Result (Array U32 22#usize × Usize)
  readSemanticAlpha : Slice U8 → Usize → Result (core.result.Result (Array aspis_core.field.QM31 10#usize × Usize) verifier.Error)
  readWeights : Slice U8 → Usize → alloc.vec.Vec aspis_core.field.QM31 → Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31 × Usize) verifier.Error)

def slicePartialEq (ops : ResumeOps) {T U : Type} (N : Usize)
    (inst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T) (Array U N) where
  eq := ops.eq inst
  ne := ops.ne inst

def verifier.resumeWithOps
  (ops : ResumeOps)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
  Result (core.result.Result (verifier.Prepared × verifier.Accumulator)
    verifier.Error)
  := do
  let i := Slice.len bytes
  let i1 ← ops.checkpointSize v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne (slicePartialEq ops
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← ops.tag v
      if i2 != i3
      then ok (core.result.Result.Err verifier.Error.Checkpoint)
      else
        let i4 ← Slice.index_usize bytes 9#usize
        if i4 > 22#u8
        then ok (core.result.Result.Err verifier.Error.Checkpoint)
        else
          let i5 ← Slice.index_usize bytes 10#usize
          if i5 != 1#u8
          then ok (core.result.Result.Err verifier.Error.Checkpoint)
          else
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := 11#usize, «end» := 16#usize }
            let i6 ← core.slice.Slice.iter s1
            let (b1, _) ← ops.headerAny i6
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← i7 - 32#usize
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize }
              let s3 ← lift (Array.to_slice (Array.make 1#usize [ proof ]))
              let a ← aspis_coredigestDigest32Inst.digest hash s3
              let b2 ←
                ops.ne core.cmp.PartialEqU8 s2 a
              if b2
              then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize }
                let s5 ←
                  lift (Array.to_slice (Array.make 1#usize [ public1 ]))
                let a1 ← aspis_coredigestDigest32Inst.digest hash s5
                let b3 ←
                  ops.ne core.cmp.PartialEqU8 s4
                    a1
                if b3
                then ok (core.result.Result.Err verifier.Error.Checkpoint)
                else
                  let s6 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                      bytes { start := end1 }
                  let s7 ←
                    lift (Array.to_slice
                      (Array.make 22#usize [
                        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
                        58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
                        99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8
                        ]))
                  let s8 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      bytes { «end» := end1 }
                  let s9 ←
                    lift (Array.to_slice (Array.make 2#usize [ s7, s8 ]))
                  let a2 ← aspis_coredigestDigest32Inst.digest hash s9
                  let b4 ←
                    ops.ne core.cmp.PartialEqU8
                      s6 a2
                  if b4
                  then ok (core.result.Result.Err verifier.Error.Checkpoint)
                  else
                    let (state, r) ←
                      ops.raw 32#usize
                        { bytes, «at» := 80#usize }
                    let (a3, r1) ← ops.raw 32#usize r
                    let (a4, r2) ← ops.raw 32#usize r1
                    let (r3, r4) ← ops.readE r2
                    let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
                    match cf with
                    | core.ops.control_flow.ControlFlow.Continue val =>
                      let (r5, r6) ← ops.readE r4
                      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
                      match cf1 with
                      | core.ops.control_flow.ControlFlow.Continue val1 =>
                        let (r7, r8) ← ops.readE r6
                        let cf2 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf2 with
                        | core.ops.control_flow.ControlFlow.Continue val2 =>
                          let (r9, r10) ← ops.readE r8
                          let cf3 ←
                            core.result.Result.Insts.CoreOpsTry.branch r9
                          match cf3 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let (r11, r12) ← ops.readK r10
                            let cf4 ←
                              core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf4 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let (queries, at1) ←
                                ops.readQueries bytes
                                  r12.«at»
                              let r13 ←
                                ops.validate queries
                              let cf5 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf5 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let r14 ←
                                  ops.readSemanticAlpha bytes
                                    at1
                                let cf6 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r14
                                match cf6 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val5 =>
                                  let (semantic_alpha, at2) := val5
                                  let (r15, r16) ←
                                    ops.readK
                                      { r12 with «at» := at2 }
                                  let cf7 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r15
                                  match cf7 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val6 =>
                                    let (r17, r18) ← ops.readK r16
                                    let cf8 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf8 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val7 =>
                                      let (r19, r20) ← ops.readK r18
                                      let cf9 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r19
                                      match cf9 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val8 =>
                                        let (r21, r22) ←
                                          ops.readK r20
                                        let cf10 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r21
                                        match cf10 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val9 =>
                                          let (r23, r24) ←
                                            ops.readE r22
                                          let cf11 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r23
                                          match cf11 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val10 =>
                                            let (r25, r26) ←
                                              ops.readE r24
                                            let cf12 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r25
                                            match cf12 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val11 =>
                                              let (r27, r28) ←
                                                ops.readK r26
                                              let cf13 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r27
                                              match cf13 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val12 =>
                                                let i8 ←
                                                  ops.finalLen v
                                                let q ←
                                                  ops.zeroK
                                                let r30 ← ops.filled i8 q
                                                let cf14 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r30
                                                match cf14 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val13 =>
                                                  let r31 ←
                                                    ops.readWeights
                                                      bytes r28.«at» val13
                                                  let cf15 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r31
                                                  match cf15 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val14 =>
                                                    let (weights, at3) := val14
                                                    if at3 != end1
                                                    then
                                                      ok
                                                        (core.result.Result.Err
                                                        verifier.Error.Checkpoint)
                                                    else
                                                      let i9 ←
                                                        lift (UScalar.cast
                                                          .Usize i4)
                                                      ok (core.result.Result.Ok
                                                        ({
                                                           variant := v,
                                                           roots :=
                                                             (Array.make
                                                                2#usize [
                                                               a3, a4
                                                               ]),
                                                           gamma := val,
                                                           kappa := val1,
                                                           alpha :=
                                                             (Array.make
                                                                2#usize [
                                                               val2, val3
                                                               ]),
                                                           rho := val4,
                                                           queries,
                                                           semantic_alpha,
                                                           z :=
                                                             (Array.make
                                                                2#usize [
                                                               {
                                                                 x := val6,
                                                                 y := val7
                                                               },
                                                               {
                                                                 x := val8,
                                                                 y := val9
                                                               }
                                                               ]),
                                                           claim := val10,
                                                           state
                                                         },
                                                        {
                                                          weights,
                                                          rhs := val11,
                                                          power := val12,
                                                          next := i9
                                                        }))
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      (verifier.Prepared ×
                                                      verifier.Accumulator)
                                                      (core.convert.FromSame
                                                      verifier.Error) residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    (verifier.Prepared ×
                                                    verifier.Accumulator)
                                                    (core.convert.FromSame
                                                    verifier.Error) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  (verifier.Prepared ×
                                                  verifier.Accumulator)
                                                  (core.convert.FromSame
                                                  verifier.Error) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (verifier.Prepared ×
                                                verifier.Accumulator)
                                                (core.convert.FromSame
                                                verifier.Error) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (verifier.Prepared ×
                                              verifier.Accumulator)
                                              (core.convert.FromSame
                                              verifier.Error) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            (verifier.Prepared ×
                                            verifier.Accumulator)
                                            (core.convert.FromSame
                                            verifier.Error) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (verifier.Prepared ×
                                          verifier.Accumulator)
                                          (core.convert.FromSame
                                          verifier.Error) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (verifier.Prepared ×
                                        verifier.Accumulator)
                                        (core.convert.FromSame verifier.Error)
                                        residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (verifier.Prepared ×
                                      verifier.Accumulator)
                                      (core.convert.FromSame verifier.Error)
                                      residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (verifier.Prepared × verifier.Accumulator)
                                    (core.convert.FromSame verifier.Error)
                                    residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (verifier.Prepared × verifier.Accumulator)
                                  (core.convert.FromSame verifier.Error)
                                  residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (verifier.Prepared × verifier.Accumulator)
                                (core.convert.FromSame verifier.Error) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (verifier.Prepared × verifier.Accumulator)
                              (core.convert.FromSame verifier.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (verifier.Prepared × verifier.Accumulator)
                            (core.convert.FromSame verifier.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (verifier.Prepared × verifier.Accumulator)
                          (core.convert.FromSame verifier.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (verifier.Prepared × verifier.Accumulator)
                        (core.convert.FromSame verifier.Error) residual

end AspisR1Stage2
