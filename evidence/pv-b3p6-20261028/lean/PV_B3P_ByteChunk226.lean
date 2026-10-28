import PV_B3P_ByteAt226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.chunk
  (p : reference226.OwnedPublic) (base : Std.Usize) :
  Result (core.result.Result (Array Std.U8 64#usize)
    aspis_core.state_only_prefix.r0.Error)
  := do
  let i ← lift (Std.Usize.wrapping_add base 0#usize)
  let r ← reference226.byte_at p i
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i1 ← lift (Std.Usize.wrapping_add base 1#usize)
    let r1 ← reference226.byte_at p i1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i2 ← lift (Std.Usize.wrapping_add base 2#usize)
      let r2 ← reference226.byte_at p i2
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i3 ← lift (Std.Usize.wrapping_add base 3#usize)
        let r3 ← reference226.byte_at p i3
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let i4 ← lift (Std.Usize.wrapping_add base 4#usize)
          let r4 ← reference226.byte_at p i4
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i5 ← lift (Std.Usize.wrapping_add base 5#usize)
            let r5 ← reference226.byte_at p i5
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i6 ← lift (Std.Usize.wrapping_add base 6#usize)
              let r6 ← reference226.byte_at p i6
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let i7 ← lift (Std.Usize.wrapping_add base 7#usize)
                let r7 ← reference226.byte_at p i7
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  let i8 ← lift (Std.Usize.wrapping_add base 8#usize)
                  let r8 ← reference226.byte_at p i8
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val8 =>
                    let i9 ← lift (Std.Usize.wrapping_add base 9#usize)
                    let r9 ← reference226.byte_at p i9
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                      let i10 ← lift (Std.Usize.wrapping_add base 10#usize)
                      let r10 ← reference226.byte_at p i10
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue val10 =>
                        let i11 ← lift (Std.Usize.wrapping_add base 11#usize)
                        let r11 ← reference226.byte_at p i11
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val11 =>
                          let i12 ←
                            lift (Std.Usize.wrapping_add base 12#usize)
                          let r12 ← reference226.byte_at p i12
                          let cf12 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf12 with
                          | core.ops.control_flow.ControlFlow.Continue val12 =>
                            let i13 ←
                              lift (Std.Usize.wrapping_add base 13#usize)
                            let r13 ← reference226.byte_at p i13
                            let cf13 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf13 with
                            | core.ops.control_flow.ControlFlow.Continue val13
                              =>
                              let i14 ←
                                lift (Std.Usize.wrapping_add base 14#usize)
                              let r14 ← reference226.byte_at p i14
                              let cf14 ←
                                core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf14 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val14 =>
                                let i15 ←
                                  lift (Std.Usize.wrapping_add base 15#usize)
                                let r15 ← reference226.byte_at p i15
                                let cf15 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf15 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val15 =>
                                  let i16 ←
                                    lift (Std.Usize.wrapping_add base 16#usize)
                                  let r16 ← reference226.byte_at p i16
                                  let cf16 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf16 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val16 =>
                                    let i17 ←
                                      lift (Std.Usize.wrapping_add base
                                        17#usize)
                                    let r17 ← reference226.byte_at p i17
                                    let cf17 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf17 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val17 =>
                                      let i18 ←
                                        lift (Std.Usize.wrapping_add base
                                          18#usize)
                                      let r18 ← reference226.byte_at p i18
                                      let cf18 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf18 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val18 =>
                                        let i19 ←
                                          lift (Std.Usize.wrapping_add base
                                            19#usize)
                                        let r19 ← reference226.byte_at p i19
                                        let cf19 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf19 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val19 =>
                                          let i20 ←
                                            lift (Std.Usize.wrapping_add base
                                              20#usize)
                                          let r20 ←
                                            reference226.byte_at p i20
                                          let cf20 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf20 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val20 =>
                                            let i21 ←
                                              lift (Std.Usize.wrapping_add base
                                                21#usize)
                                            let r21 ←
                                              reference226.byte_at p i21
                                            let cf21 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r21
                                            match cf21 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val21 =>
                                              let i22 ←
                                                lift (Std.Usize.wrapping_add
                                                  base 22#usize)
                                              let r22 ←
                                                reference226.byte_at p i22
                                              let cf22 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r22
                                              match cf22 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val22 =>
                                                let i23 ←
                                                  lift (Std.Usize.wrapping_add
                                                    base 23#usize)
                                                let r23 ←
                                                  reference226.byte_at p i23
                                                let cf23 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r23
                                                match cf23 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val23 =>
                                                  let i24 ←
                                                    lift
                                                      (Std.Usize.wrapping_add
                                                      base 24#usize)
                                                  let r24 ←
                                                    reference226.byte_at p i24
                                                  let cf24 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r24
                                                  match cf24 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val24 =>
                                                    let i25 ←
                                                      lift
                                                        (Std.Usize.wrapping_add
                                                        base 25#usize)
                                                    let r25 ←
                                                      reference226.byte_at p
                                                        i25
                                                    let cf25 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r25
                                                    match cf25 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val25 =>
                                                      let i26 ←
                                                        lift
                                                          (Std.Usize.wrapping_add
                                                          base 26#usize)
                                                      let r26 ←
                                                        reference226.byte_at p
                                                          i26
                                                      let cf26 ←
                                                        core.result.Result.Insts.CoreOpsTry.branch
                                                          r26
                                                      match cf26 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        val26 =>
                                                        let i27 ←
                                                          lift
                                                            (Std.Usize.wrapping_add
                                                            base 27#usize)
                                                        let r27 ←
                                                          reference226.byte_at
                                                            p i27
                                                        let cf27 ←
                                                          core.result.Result.Insts.CoreOpsTry.branch
                                                            r27
                                                        match cf27 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          val27 =>
                                                          let i28 ←
                                                            lift
                                                              (Std.Usize.wrapping_add
                                                              base 28#usize)
                                                          let r28 ←
                                                            reference226.byte_at
                                                              p i28
                                                          let cf28 ←
                                                            core.result.Result.Insts.CoreOpsTry.branch
                                                              r28
                                                          match cf28 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            val28 =>
                                                            let i29 ←
                                                              lift
                                                                (Std.Usize.wrapping_add
                                                                base 29#usize)
                                                            let r29 ←
                                                              reference226.byte_at
                                                                p i29
                                                            let cf29 ←
                                                              core.result.Result.Insts.CoreOpsTry.branch
                                                                r29
                                                            match cf29 with
                                                            |
                                                              core.ops.control_flow.ControlFlow.Continue
                                                              val29 =>
                                                              let i30 ←
                                                                lift
                                                                  (Std.Usize.wrapping_add
                                                                  base
                                                                  30#usize)
                                                              let r30 ←
                                                                reference226.byte_at
                                                                  p i30
                                                              let cf30 ←
                                                                core.result.Result.Insts.CoreOpsTry.branch
                                                                  r30
                                                              match cf30 with
                                                              |
                                                                core.ops.control_flow.ControlFlow.Continue
                                                                val30 =>
                                                                let i31 ←
                                                                  lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    31#usize)
                                                                let r31 ←
                                                                  reference226.byte_at
                                                                    p i31
                                                                let cf31 ←
                                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                                    r31
                                                                match cf31 with
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Continue
                                                                  val31 =>
                                                                  let i32 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    32#usize)
                                                                  let r32 ←
                                                                    reference226.byte_at
                                                                    p i32
                                                                  let cf32 ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r32
                                                                  match cf32
                                                                    with
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val32 =>
                                                                    let i33 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    33#usize)
                                                                    let r33 ←
                                                                    reference226.byte_at
                                                                    p i33
                                                                    let cf33
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r33
                                                                    match cf33
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val33 =>
                                                                    let i34 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    34#usize)
                                                                    let r34 ←
                                                                    reference226.byte_at
                                                                    p i34
                                                                    let cf34
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r34
                                                                    match cf34
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val34 =>
                                                                    let i35 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    35#usize)
                                                                    let r35 ←
                                                                    reference226.byte_at
                                                                    p i35
                                                                    let cf35
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r35
                                                                    match cf35
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val35 =>
                                                                    let i36 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    36#usize)
                                                                    let r36 ←
                                                                    reference226.byte_at
                                                                    p i36
                                                                    let cf36
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r36
                                                                    match cf36
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val36 =>
                                                                    let i37 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    37#usize)
                                                                    let r37 ←
                                                                    reference226.byte_at
                                                                    p i37
                                                                    let cf37
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r37
                                                                    match cf37
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val37 =>
                                                                    let i38 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    38#usize)
                                                                    let r38 ←
                                                                    reference226.byte_at
                                                                    p i38
                                                                    let cf38
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r38
                                                                    match cf38
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val38 =>
                                                                    let i39 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    39#usize)
                                                                    let r39 ←
                                                                    reference226.byte_at
                                                                    p i39
                                                                    let cf39
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r39
                                                                    match cf39
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val39 =>
                                                                    let i40 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    40#usize)
                                                                    let r40 ←
                                                                    reference226.byte_at
                                                                    p i40
                                                                    let cf40
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r40
                                                                    match cf40
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val40 =>
                                                                    let i41 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    41#usize)
                                                                    let r41 ←
                                                                    reference226.byte_at
                                                                    p i41
                                                                    let cf41
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r41
                                                                    match cf41
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val41 =>
                                                                    let i42 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    42#usize)
                                                                    let r42 ←
                                                                    reference226.byte_at
                                                                    p i42
                                                                    let cf42
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r42
                                                                    match cf42
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val42 =>
                                                                    let i43 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    43#usize)
                                                                    let r43 ←
                                                                    reference226.byte_at
                                                                    p i43
                                                                    let cf43
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r43
                                                                    match cf43
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val43 =>
                                                                    let i44 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    44#usize)
                                                                    let r44 ←
                                                                    reference226.byte_at
                                                                    p i44
                                                                    let cf44
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r44
                                                                    match cf44
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val44 =>
                                                                    let i45 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    45#usize)
                                                                    let r45 ←
                                                                    reference226.byte_at
                                                                    p i45
                                                                    let cf45
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r45
                                                                    match cf45
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val45 =>
                                                                    let i46 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    46#usize)
                                                                    let r46 ←
                                                                    reference226.byte_at
                                                                    p i46
                                                                    let cf46
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r46
                                                                    match cf46
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val46 =>
                                                                    let i47 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    47#usize)
                                                                    let r47 ←
                                                                    reference226.byte_at
                                                                    p i47
                                                                    let cf47
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r47
                                                                    match cf47
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val47 =>
                                                                    let i48 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    48#usize)
                                                                    let r48 ←
                                                                    reference226.byte_at
                                                                    p i48
                                                                    let cf48
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r48
                                                                    match cf48
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val48 =>
                                                                    let i49 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    49#usize)
                                                                    let r49 ←
                                                                    reference226.byte_at
                                                                    p i49
                                                                    let cf49
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r49
                                                                    match cf49
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val49 =>
                                                                    let i50 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    50#usize)
                                                                    let r50 ←
                                                                    reference226.byte_at
                                                                    p i50
                                                                    let cf50
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r50
                                                                    match cf50
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val50 =>
                                                                    let i51 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    51#usize)
                                                                    let r51 ←
                                                                    reference226.byte_at
                                                                    p i51
                                                                    let cf51
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r51
                                                                    match cf51
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val51 =>
                                                                    let i52 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    52#usize)
                                                                    let r52 ←
                                                                    reference226.byte_at
                                                                    p i52
                                                                    let cf52
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r52
                                                                    match cf52
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val52 =>
                                                                    let i53 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    53#usize)
                                                                    let r53 ←
                                                                    reference226.byte_at
                                                                    p i53
                                                                    let cf53
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r53
                                                                    match cf53
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val53 =>
                                                                    let i54 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    54#usize)
                                                                    let r54 ←
                                                                    reference226.byte_at
                                                                    p i54
                                                                    let cf54
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r54
                                                                    match cf54
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val54 =>
                                                                    let i55 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    55#usize)
                                                                    let r55 ←
                                                                    reference226.byte_at
                                                                    p i55
                                                                    let cf55
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r55
                                                                    match cf55
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val55 =>
                                                                    let i56 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    56#usize)
                                                                    let r56 ←
                                                                    reference226.byte_at
                                                                    p i56
                                                                    let cf56
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r56
                                                                    match cf56
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val56 =>
                                                                    let i57 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    57#usize)
                                                                    let r57 ←
                                                                    reference226.byte_at
                                                                    p i57
                                                                    let cf57
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r57
                                                                    match cf57
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val57 =>
                                                                    let i58 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    58#usize)
                                                                    let r58 ←
                                                                    reference226.byte_at
                                                                    p i58
                                                                    let cf58
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r58
                                                                    match cf58
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val58 =>
                                                                    let i59 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    59#usize)
                                                                    let r59 ←
                                                                    reference226.byte_at
                                                                    p i59
                                                                    let cf59
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r59
                                                                    match cf59
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val59 =>
                                                                    let i60 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    60#usize)
                                                                    let r60 ←
                                                                    reference226.byte_at
                                                                    p i60
                                                                    let cf60
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r60
                                                                    match cf60
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val60 =>
                                                                    let i61 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    61#usize)
                                                                    let r61 ←
                                                                    reference226.byte_at
                                                                    p i61
                                                                    let cf61
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r61
                                                                    match cf61
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val61 =>
                                                                    let i62 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    62#usize)
                                                                    let r62 ←
                                                                    reference226.byte_at
                                                                    p i62
                                                                    let cf62
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r62
                                                                    match cf62
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val62 =>
                                                                    let i63 ←
                                                                    lift
                                                                    (Std.Usize.wrapping_add
                                                                    base
                                                                    63#usize)
                                                                    let r63 ←
                                                                    reference226.byte_at
                                                                    p i63
                                                                    let cf63
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r63
                                                                    match cf63
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val63 =>
                                                                    ok
                                                                    (core.result.Result.Ok
                                                                    (Array.make
                                                                    64#usize [
                                                                    val, val1,
                                                                    val2, val3,
                                                                    val4, val5,
                                                                    val6, val7,
                                                                    val8, val9,
                                                                    val10,
                                                                    val11,
                                                                    val12,
                                                                    val13,
                                                                    val14,
                                                                    val15,
                                                                    val16,
                                                                    val17,
                                                                    val18,
                                                                    val19,
                                                                    val20,
                                                                    val21,
                                                                    val22,
                                                                    val23,
                                                                    val24,
                                                                    val25,
                                                                    val26,
                                                                    val27,
                                                                    val28,
                                                                    val29,
                                                                    val30,
                                                                    val31,
                                                                    val32,
                                                                    val33,
                                                                    val34,
                                                                    val35,
                                                                    val36,
                                                                    val37,
                                                                    val38,
                                                                    val39,
                                                                    val40,
                                                                    val41,
                                                                    val42,
                                                                    val43,
                                                                    val44,
                                                                    val45,
                                                                    val46,
                                                                    val47,
                                                                    val48,
                                                                    val49,
                                                                    val50,
                                                                    val51,
                                                                    val52,
                                                                    val53,
                                                                    val54,
                                                                    val55,
                                                                    val56,
                                                                    val57,
                                                                    val58,
                                                                    val59,
                                                                    val60,
                                                                    val61,
                                                                    val62,
                                                                    val63
                                                                    ]))
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Break
                                                                  residual =>
                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (Array
                                                                    Std.U8
                                                                    64#usize)
                                                                    (core.convert.FromSame
                                                                    aspis_core.state_only_prefix.r0.Error)
                                                                    residual
                                                              |
                                                                core.ops.control_flow.ControlFlow.Break
                                                                residual =>
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                  (Array Std.U8
                                                                  64#usize)
                                                                  (core.convert.FromSame
                                                                  aspis_core.state_only_prefix.r0.Error)
                                                                  residual
                                                            |
                                                              core.ops.control_flow.ControlFlow.Break
                                                              residual =>
                                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                (Array Std.U8
                                                                64#usize)
                                                                (core.convert.FromSame
                                                                aspis_core.state_only_prefix.r0.Error)
                                                                residual
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                              (Array Std.U8
                                                              64#usize)
                                                              (core.convert.FromSame
                                                              aspis_core.state_only_prefix.r0.Error)
                                                              residual
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                            (Array Std.U8
                                                            64#usize)
                                                            (core.convert.FromSame
                                                            aspis_core.state_only_prefix.r0.Error)
                                                            residual
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                          (Array Std.U8
                                                          64#usize)
                                                          (core.convert.FromSame
                                                          aspis_core.state_only_prefix.r0.Error)
                                                          residual
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        (Array Std.U8 64#usize)
                                                        (core.convert.FromSame
                                                        aspis_core.state_only_prefix.r0.Error)
                                                        residual
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                      (Array Std.U8 64#usize)
                                                      (core.convert.FromSame
                                                      aspis_core.state_only_prefix.r0.Error)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    (Array Std.U8 64#usize)
                                                    (core.convert.FromSame
                                                    aspis_core.state_only_prefix.r0.Error)
                                                    residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  (Array Std.U8 64#usize)
                                                  (core.convert.FromSame
                                                  aspis_core.state_only_prefix.r0.Error)
                                                  residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (Array Std.U8 64#usize)
                                                (core.convert.FromSame
                                                aspis_core.state_only_prefix.r0.Error)
                                                residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (Array Std.U8 64#usize)
                                              (core.convert.FromSame
                                              aspis_core.state_only_prefix.r0.Error)
                                              residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            (Array Std.U8 64#usize)
                                            (core.convert.FromSame
                                            aspis_core.state_only_prefix.r0.Error)
                                            residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (Array Std.U8 64#usize)
                                          (core.convert.FromSame
                                          aspis_core.state_only_prefix.r0.Error)
                                          residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (Array Std.U8 64#usize)
                                        (core.convert.FromSame
                                        aspis_core.state_only_prefix.r0.Error)
                                        residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (Array Std.U8 64#usize)
                                      (core.convert.FromSame
                                      aspis_core.state_only_prefix.r0.Error)
                                      residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (Array Std.U8 64#usize)
                                    (core.convert.FromSame
                                    aspis_core.state_only_prefix.r0.Error)
                                    residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (Array Std.U8 64#usize)
                                  (core.convert.FromSame
                                  aspis_core.state_only_prefix.r0.Error)
                                  residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (Array Std.U8 64#usize) (core.convert.FromSame
                                aspis_core.state_only_prefix.r0.Error) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (Array Std.U8 64#usize) (core.convert.FromSame
                              aspis_core.state_only_prefix.r0.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (Array Std.U8 64#usize) (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (Array Std.U8 64#usize) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (Array Std.U8 64#usize) (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (Array Std.U8 64#usize) (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (Array Std.U8 64#usize) (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (Array Std.U8 64#usize) (core.convert.FromSame
                  aspis_core.state_only_prefix.r0.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Array Std.U8 64#usize) (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Array Std.U8 64#usize) (core.convert.FromSame
              aspis_core.state_only_prefix.r0.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array Std.U8 64#usize) (core.convert.FromSame
            aspis_core.state_only_prefix.r0.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array Std.U8 64#usize) (core.convert.FromSame
          aspis_core.state_only_prefix.r0.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U8 64#usize) (core.convert.FromSame
        aspis_core.state_only_prefix.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 64#usize) (core.convert.FromSame
      aspis_core.state_only_prefix.r0.Error) residual


end PV_B3P_226
#print axioms PV_B3P_226.reference226.chunk
