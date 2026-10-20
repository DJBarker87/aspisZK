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
                              let (a5, r13) ← ops.raw 4#usize r12
                              let i8 ← lift (core.num.U32.from_le_bytes a5)
                              let (a6, r14) ← ops.raw 4#usize r13
                              let i9 ← lift (core.num.U32.from_le_bytes a6)
                              let (a7, r15) ← ops.raw 4#usize r14
                              let i10 ← lift (core.num.U32.from_le_bytes a7)
                              let (a8, r16) ← ops.raw 4#usize r15
                              let i11 ← lift (core.num.U32.from_le_bytes a8)
                              let (a9, r17) ← ops.raw 4#usize r16
                              let i12 ← lift (core.num.U32.from_le_bytes a9)
                              let (a10, r18) ←
                                ops.raw 4#usize r17
                              let i13 ← lift (core.num.U32.from_le_bytes a10)
                              let (a11, r19) ←
                                ops.raw 4#usize r18
                              let i14 ← lift (core.num.U32.from_le_bytes a11)
                              let (a12, r20) ←
                                ops.raw 4#usize r19
                              let i15 ← lift (core.num.U32.from_le_bytes a12)
                              let (a13, r21) ←
                                ops.raw 4#usize r20
                              let i16 ← lift (core.num.U32.from_le_bytes a13)
                              let (a14, r22) ←
                                ops.raw 4#usize r21
                              let i17 ← lift (core.num.U32.from_le_bytes a14)
                              let (a15, r23) ←
                                ops.raw 4#usize r22
                              let i18 ← lift (core.num.U32.from_le_bytes a15)
                              let (a16, r24) ←
                                ops.raw 4#usize r23
                              let i19 ← lift (core.num.U32.from_le_bytes a16)
                              let (a17, r25) ←
                                ops.raw 4#usize r24
                              let i20 ← lift (core.num.U32.from_le_bytes a17)
                              let (a18, r26) ←
                                ops.raw 4#usize r25
                              let i21 ← lift (core.num.U32.from_le_bytes a18)
                              let (a19, r27) ←
                                ops.raw 4#usize r26
                              let i22 ← lift (core.num.U32.from_le_bytes a19)
                              let (a20, r28) ←
                                ops.raw 4#usize r27
                              let i23 ← lift (core.num.U32.from_le_bytes a20)
                              let (a21, r29) ←
                                ops.raw 4#usize r28
                              let i24 ← lift (core.num.U32.from_le_bytes a21)
                              let (a22, r30) ←
                                ops.raw 4#usize r29
                              let i25 ← lift (core.num.U32.from_le_bytes a22)
                              let (a23, r31) ←
                                ops.raw 4#usize r30
                              let i26 ← lift (core.num.U32.from_le_bytes a23)
                              let (a24, r32) ←
                                ops.raw 4#usize r31
                              let i27 ← lift (core.num.U32.from_le_bytes a24)
                              let (a25, r33) ←
                                ops.raw 4#usize r32
                              let i28 ← lift (core.num.U32.from_le_bytes a25)
                              let (a26, r34) ←
                                ops.raw 4#usize r33
                              let i29 ← lift (core.num.U32.from_le_bytes a26)
                              let r35 ←
                                ops.validate
                                  (Array.make 22#usize [
                                    i8, i9, i10, i11, i12, i13, i14, i15, i16,
                                    i17, i18, i19, i20, i21, i22, i23, i24,
                                    i25, i26, i27, i28, i29
                                    ])
                              let cf5 ←
                                core.result.Result.Insts.CoreOpsTry.branch r35
                              match cf5 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let (r36, r37) ← ops.readK r34
                                let cf6 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r36
                                match cf6 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val5 =>
                                  let (r38, r39) ← ops.readK r37
                                  let cf7 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r38
                                  match cf7 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val6 =>
                                    let (r40, r41) ← ops.readK r39
                                    let cf8 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r40
                                    match cf8 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val7 =>
                                      let (r42, r43) ← ops.readK r41
                                      let cf9 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r42
                                      match cf9 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val8 =>
                                        let (r44, r45) ←
                                          ops.readK r43
                                        let cf10 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r44
                                        match cf10 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val9 =>
                                          let (r46, r47) ←
                                            ops.readK r45
                                          let cf11 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r46
                                          match cf11 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val10 =>
                                            let (r48, r49) ←
                                              ops.readK r47
                                            let cf12 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r48
                                            match cf12 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val11 =>
                                              let (r50, r51) ←
                                                ops.readK r49
                                              let cf13 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r50
                                              match cf13 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val12 =>
                                                let (r52, r53) ←
                                                  ops.readK r51
                                                let cf14 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r52
                                                match cf14 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val13 =>
                                                  let (r54, r55) ←
                                                    ops.readK r53
                                                  let cf15 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r54
                                                  match cf15 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val14 =>
                                                    let (r56, r57) ←
                                                      ops.readK r55
                                                    let cf16 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r56
                                                    match cf16 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val15 =>
                                                      let (r58, r59) ←
                                                        ops.readK r57
                                                      let cf17 ←
                                                        core.result.Result.Insts.CoreOpsTry.branch
                                                          r58
                                                      match cf17 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        val16 =>
                                                        let (r60, r61) ←
                                                          ops.readK r59
                                                        let cf18 ←
                                                          core.result.Result.Insts.CoreOpsTry.branch
                                                            r60
                                                        match cf18 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          val17 =>
                                                          let (r62, r63) ←
                                                            ops.readK
                                                              r61
                                                          let cf19 ←
                                                            core.result.Result.Insts.CoreOpsTry.branch
                                                              r62
                                                          match cf19 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            val18 =>
                                                            let (r64, r65) ←
                                                              ops.readE
                                                                r63
                                                            let cf20 ←
                                                              core.result.Result.Insts.CoreOpsTry.branch
                                                                r64
                                                            match cf20 with
                                                            |
                                                              core.ops.control_flow.ControlFlow.Continue
                                                              val19 =>
                                                              let (r66, r67)
                                                                ←
                                                                ops.readE
                                                                  r65
                                                              let cf21 ←
                                                                core.result.Result.Insts.CoreOpsTry.branch
                                                                  r66
                                                              match cf21 with
                                                              |
                                                                core.ops.control_flow.ControlFlow.Continue
                                                                val20 =>
                                                                let (r68, r69)
                                                                  ←
                                                                  ops.readK
                                                                    r67
                                                                let cf22 ←
                                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                                    r68
                                                                match cf22 with
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Continue
                                                                  val21 =>
                                                                  let i30 ←
                                                                    ops.finalLen
                                                                    v
                                                                  let q ←
                                                                    ops.zeroK
                                                                  let r71 ← ops.filled i30 q
                                                                  let cf23 ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r71
                                                                  match cf23
                                                                    with
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val22 =>
                                                                    let r72 ←
                                                                    ops.readWeights
                                                                    bytes
                                                                    r69.«at»
                                                                    val22
                                                                    let cf24
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r72
                                                                    match cf24
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val23 =>
                                                                    let
                                                                    (weights,
                                                                    at1) :=
                                                                    val23
                                                                    if at1 !=
                                                                    end1
                                                                    then
                                                                    ok
                                                                    (core.result.Result.Err
                                                                    verifier.Error.Checkpoint)
                                                                    else
                                                                    let i31 ←
                                                                    lift
                                                                    (UScalar.cast
                                                                    .Usize i4)
                                                                    ok
                                                                    (core.result.Result.Ok
                                                                    ({
                                                                    variant :=
                                                                    v,
                                                                    roots :=
                                                                    (Array.make
                                                                    2#usize [
                                                                    a3, a4
                                                                    ]),
                                                                    gamma :=
                                                                    val,
                                                                    kappa :=
                                                                    val1,
                                                                    alpha :=
                                                                    (Array.make
                                                                    2#usize [
                                                                    val2, val3
                                                                    ]),
                                                                    rho := val4,
                                                                    queries :=
                                                                    (Array.make
                                                                    22#usize [
                                                                    i8, i9,
                                                                    i10, i11,
                                                                    i12, i13,
                                                                    i14, i15,
                                                                    i16, i17,
                                                                    i18, i19,
                                                                    i20, i21,
                                                                    i22, i23,
                                                                    i24, i25,
                                                                    i26, i27,
                                                                    i28, i29
                                                                    ]),
                                                                    semantic_alpha :=
                                                                    (Array.make
                                                                    10#usize [
                                                                    val5, val6,
                                                                    val7, val8,
                                                                    val9,
                                                                    val10,
                                                                    val11,
                                                                    val12,
                                                                    val13,
                                                                    val14
                                                                    ]),
                                                                    z :=
                                                                    (Array.make
                                                                    2#usize [
                                                                    {
                                                                    x := val15,
                                                                    y := val16
                                                                    },
                                                                    {
                                                                    x := val17,
                                                                    y := val18
                                                                    }
                                                                    ]),
                                                                    claim :=
                                                                    val19,
                                                                    state
                                                                    },
                                                                    {
                                                                    weights,
                                                                    rhs :=
                                                                    val20,
                                                                    power :=
                                                                    val21,
                                                                    next := i31
                                                                    }))
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (verifier.Prepared
                                                                    ×
                                                                    verifier.Accumulator)
                                                                    (core.convert.FromSame
                                                                    verifier.Error)
                                                                    residual
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (verifier.Prepared
                                                                    ×
                                                                    verifier.Accumulator)
                                                                    (core.convert.FromSame
                                                                    verifier.Error)
                                                                    residual
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Break
                                                                  residual =>
                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (verifier.Prepared
                                                                    ×
                                                                    verifier.Accumulator)
                                                                    (core.convert.FromSame
                                                                    verifier.Error)
                                                                    residual
                                                              |
                                                                core.ops.control_flow.ControlFlow.Break
                                                                residual =>
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                  (verifier.Prepared
                                                                  ×
                                                                  verifier.Accumulator)
                                                                  (core.convert.FromSame
                                                                  verifier.Error)
                                                                  residual
                                                            |
                                                              core.ops.control_flow.ControlFlow.Break
                                                              residual =>
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                (verifier.Prepared
                                                                ×
                                                                verifier.Accumulator)
                                                                (core.convert.FromSame
                                                                verifier.Error)
                                                                residual
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                              (verifier.Prepared
                                                              ×
                                                              verifier.Accumulator)
                                                              (core.convert.FromSame
                                                              verifier.Error)
                                                              residual
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                            (verifier.Prepared
                                                            ×
                                                            verifier.Accumulator)
                                                            (core.convert.FromSame
                                                            verifier.Error)
                                                            residual
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                          (verifier.Prepared ×
                                                          verifier.Accumulator)
                                                          (core.convert.FromSame
                                                          verifier.Error)
                                                          residual
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        (verifier.Prepared ×
                                                        verifier.Accumulator)
                                                        (core.convert.FromSame
                                                        verifier.Error)
                                                        residual
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
