import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation

structure RoundModel.Boundaries where
  decode : (N : Usize) → r1_wire.ValidatedRecord → Usize →
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)
  boundary : Array aspis_core.field.QM31 28#usize → Result aspis_core.field.QM31
  value : Array aspis_core.field.QM31 28#usize → Array aspis_core.field.QM31 10#usize → Usize → Result aspis_core.field.QM31
def aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : aspis_core.field.CM31) (other : aspis_core.field.CM31) :
  Result Bool
  := do
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.a other.a
  if b
  then aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self.b other.b
  else ok false

def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  (self : aspis_core.field.QM31) (other : aspis_core.field.QM31) :
  Result Bool
  := do
  let b ←
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c0 other.c0
  if b
  then aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq self.c1 other.c1
  else ok false


@[reducible]
impl_def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 : core.cmp.PartialEq
  aspis_core.field.QM31 aspis_core.field.QM31 := {
  eq := aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
}

def RoundModel.rounds (B : RoundModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 14#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let r1 ← B.decode 1#usize vr 0#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let running ← Array.index_usize val 0#usize
      let alpha := Array.repeat 10#usize aspis_core.field.QM31.ZERO
      let i ← lift (UScalar.cast .U8 0#usize)
      let row ← 15#u8 + i
      let r2 ← r1_wire.Prefix.validated_record prefix1 row
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue vr1 =>
        let r3 ← B.decode 28#usize vr1 0#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let boundary ← B.boundary val1
          let b ←
            core.cmp.PartialEq.ne.trait_default
              aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 boundary running
          if b
          then ok (core.result.Result.Err (r1_wire.Error.Boundary 0#usize))
          else
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue vr2 =>
              let (r4, transcript1) ←
                r1_wire.SemanticTranscript.semantic_validated
                  aspis_coreDigest32Inst transcript vr2
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val2 =>
                let alpha1 ← Array.update alpha 0#usize val2
                let value ← B.value val1 alpha1 0#usize
                let i1 ← lift (UScalar.cast .U8 1#usize)
                let row1 ← 15#u8 + i1
                let r5 ← r1_wire.Prefix.validated_record prefix1 row1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue vr3 =>
                  let r6 ←
                    B.decode 28#usize vr3 0#usize
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val3 =>
                    let boundary1 ← B.boundary val3
                    let b1 ←
                      core.cmp.PartialEq.ne.trait_default
                        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                        boundary1 value
                    if b1
                    then
                      ok (core.result.Result.Err (r1_wire.Error.Boundary
                        1#usize))
                    else
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r5
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue vr4 =>
                        let (r7, transcript2) ←
                          r1_wire.SemanticTranscript.semantic_validated
                            aspis_coreDigest32Inst transcript1 vr4
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val4 =>
                          let alpha2 ← Array.update alpha1 1#usize val4
                          let value1 ←
                            B.value val3 alpha2 1#usize
                          let i2 ← lift (UScalar.cast .U8 2#usize)
                          let row2 ← 15#u8 + i2
                          let r8 ←
                            r1_wire.Prefix.validated_record prefix1 row2
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r8
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue vr5 =>
                            let r9 ←
                              B.decode 28#usize vr5
                                0#usize
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let boundary2 ←
                                B.boundary val5
                              let b2 ←
                                core.cmp.PartialEq.ne.trait_default
                                  aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                  boundary2 value1
                              if b2
                              then
                                ok (core.result.Result.Err
                                  (r1_wire.Error.Boundary 2#usize))
                              else
                                let cf12 ←
                                  core.result.Result.Insts.CoreOpsTry.branch r8
                                match cf12 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  vr6 =>
                                  let (r10, transcript3) ←
                                    r1_wire.SemanticTranscript.semantic_validated
                                      aspis_coreDigest32Inst transcript2 vr6
                                  let cf13 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r10
                                  match cf13 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val6 =>
                                    let alpha3 ←
                                      Array.update alpha2 2#usize val6
                                    let value2 ←
                                      B.value val5 alpha3
                                        2#usize
                                    let i3 ← lift (UScalar.cast .U8 3#usize)
                                    let row3 ← 15#u8 + i3
                                    let r11 ←
                                      r1_wire.Prefix.validated_record prefix1
                                        row3
                                    let cf14 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r11
                                    match cf14 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      vr7 =>
                                      let r12 ←
                                        B.decode
                                          28#usize vr7 0#usize
                                      let cf15 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r12
                                      match cf15 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val7 =>
                                        let boundary3 ←
                                          B.boundary val7
                                        let b3 ←
                                          core.cmp.PartialEq.ne.trait_default
                                            aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                            boundary3 value2
                                        if b3
                                        then
                                          ok (core.result.Result.Err
                                            (r1_wire.Error.Boundary 3#usize))
                                        else
                                          let cf16 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r11
                                          match cf16 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            vr8 =>
                                            let (r13, transcript4) ←
                                              r1_wire.SemanticTranscript.semantic_validated
                                                aspis_coreDigest32Inst
                                                transcript3 vr8
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r13
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val8 =>
                                              let alpha4 ←
                                                Array.update alpha3 3#usize
                                                  val8
                                              let value3 ←
                                                B.value val7
                                                  alpha4 3#usize
                                              let i4 ←
                                                lift (UScalar.cast .U8 4#usize)
                                              let row4 ← 15#u8 + i4
                                              let r14 ←
                                                r1_wire.Prefix.validated_record
                                                  prefix1 row4
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r14
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                vr9 =>
                                                let r15 ←
                                                  B.decode
                                                    28#usize vr9 0#usize
                                                let cf19 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r15
                                                match cf19 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val9 =>
                                                  let boundary4 ←
                                                    B.boundary
                                                      val9
                                                  let b4 ←
                                                    core.cmp.PartialEq.ne.trait_default
                                                      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                      boundary4 value3
                                                  if b4
                                                  then
                                                    ok (core.result.Result.Err
                                                      (r1_wire.Error.Boundary
                                                      4#usize))
                                                  else
                                                    let cf20 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r14
                                                    match cf20 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      vr10 =>
                                                      let (r16, transcript5)
                                                        ←
                                                        r1_wire.SemanticTranscript.semantic_validated
                                                          aspis_coreDigest32Inst
                                                          transcript4 vr10
                                                      let cf21 ←
                                                        core.result.Result.Insts.CoreOpsTry.branch
                                                          r16
                                                      match cf21 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        val10 =>
                                                        let alpha5 ←
                                                          Array.update alpha4
                                                            4#usize val10
                                                        let value4 ←
                                                          B.value
                                                            val9 alpha5 4#usize
                                                        let i5 ←
                                                          lift (UScalar.cast
                                                            .U8 5#usize)
                                                        let row5 ← 15#u8 + i5
                                                        let r17 ←
                                                          r1_wire.Prefix.validated_record
                                                            prefix1 row5
                                                        let cf22 ←
                                                          core.result.Result.Insts.CoreOpsTry.branch
                                                            r17
                                                        match cf22 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          vr11 =>
                                                          let r18 ←
                                                            B.decode
                                                              28#usize vr11
                                                              0#usize
                                                          let cf23 ←
                                                            core.result.Result.Insts.CoreOpsTry.branch
                                                              r18
                                                          match cf23 with
                                                          |
                                                            core.ops.control_flow.ControlFlow.Continue
                                                            val11 =>
                                                            let boundary5 ←
                                                              B.boundary
                                                                val11
                                                            let b5 ←
                                                              core.cmp.PartialEq.ne.trait_default
                                                                aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                boundary5
                                                                value4
                                                            if b5
                                                            then
                                                              ok
                                                                (core.result.Result.Err
                                                                (r1_wire.Error.Boundary
                                                                5#usize))
                                                            else
                                                              let cf24 ←
                                                                core.result.Result.Insts.CoreOpsTry.branch
                                                                  r17
                                                              match cf24 with
                                                              |
                                                                core.ops.control_flow.ControlFlow.Continue
                                                                vr12 =>
                                                                let (r19,
                                                                  transcript6)
                                                                  ←
                                                                  r1_wire.SemanticTranscript.semantic_validated
                                                                    aspis_coreDigest32Inst
                                                                    transcript5
                                                                    vr12
                                                                let cf25 ←
                                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                                    r19
                                                                match cf25 with
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Continue
                                                                  val12 =>
                                                                  let alpha6
                                                                    ←
                                                                    Array.update
                                                                    alpha5
                                                                    5#usize
                                                                    val12
                                                                  let value5
                                                                    ←
                                                                    B.value
                                                                    val11
                                                                    alpha6
                                                                    5#usize
                                                                  let i6 ←
                                                                    lift
                                                                    (UScalar.cast
                                                                    .U8
                                                                    6#usize)
                                                                  let row6 ←
                                                                    15#u8 + i6
                                                                  let r20 ←
                                                                    r1_wire.Prefix.validated_record
                                                                    prefix1
                                                                    row6
                                                                  let cf26 ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r20
                                                                  match cf26
                                                                    with
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr13 =>
                                                                    let r21 ←
                                                                    B.decode
                                                                    28#usize
                                                                    vr13
                                                                    0#usize
                                                                    let cf27
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r21
                                                                    match cf27
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val13 =>
                                                                    let
                                                                    boundary6
                                                                    ←
                                                                    B.boundary
                                                                    val13
                                                                    let b6 ←
                                                                    core.cmp.PartialEq.ne.trait_default
                                                                    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                    boundary6
                                                                    value5
                                                                    if b6
                                                                    then
                                                                    ok
                                                                    (core.result.Result.Err
                                                                    (r1_wire.Error.Boundary
                                                                    6#usize))
                                                                    else
                                                                    let cf28
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r20
                                                                    match cf28
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr14 =>
                                                                    let (r22,
                                                                    transcript7)
                                                                    ←
                                                                    r1_wire.SemanticTranscript.semantic_validated
                                                                    aspis_coreDigest32Inst
                                                                    transcript6
                                                                    vr14
                                                                    let cf29
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r22
                                                                    match cf29
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val14 =>
                                                                    let alpha7
                                                                    ←
                                                                    Array.update
                                                                    alpha6
                                                                    6#usize
                                                                    val14
                                                                    let value6
                                                                    ←
                                                                    B.value
                                                                    val13
                                                                    alpha7
                                                                    6#usize
                                                                    let i7 ←
                                                                    lift
                                                                    (UScalar.cast
                                                                    .U8
                                                                    7#usize)
                                                                    let row7
                                                                    ←
                                                                    15#u8 + i7
                                                                    let r23 ←
                                                                    r1_wire.Prefix.validated_record
                                                                    prefix1
                                                                    row7
                                                                    let cf30
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r23
                                                                    match cf30
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr15 =>
                                                                    let r24 ←
                                                                    B.decode
                                                                    28#usize
                                                                    vr15
                                                                    0#usize
                                                                    let cf31
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r24
                                                                    match cf31
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val15 =>
                                                                    let
                                                                    boundary7
                                                                    ←
                                                                    B.boundary
                                                                    val15
                                                                    let b7 ←
                                                                    core.cmp.PartialEq.ne.trait_default
                                                                    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                    boundary7
                                                                    value6
                                                                    if b7
                                                                    then
                                                                    ok
                                                                    (core.result.Result.Err
                                                                    (r1_wire.Error.Boundary
                                                                    7#usize))
                                                                    else
                                                                    let cf32
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r23
                                                                    match cf32
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr16 =>
                                                                    let (r25,
                                                                    transcript8)
                                                                    ←
                                                                    r1_wire.SemanticTranscript.semantic_validated
                                                                    aspis_coreDigest32Inst
                                                                    transcript7
                                                                    vr16
                                                                    let cf33
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r25
                                                                    match cf33
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val16 =>
                                                                    let alpha8
                                                                    ←
                                                                    Array.update
                                                                    alpha7
                                                                    7#usize
                                                                    val16
                                                                    let value7
                                                                    ←
                                                                    B.value
                                                                    val15
                                                                    alpha8
                                                                    7#usize
                                                                    let i8 ←
                                                                    lift
                                                                    (UScalar.cast
                                                                    .U8
                                                                    8#usize)
                                                                    let row8
                                                                    ←
                                                                    15#u8 + i8
                                                                    let r26 ←
                                                                    r1_wire.Prefix.validated_record
                                                                    prefix1
                                                                    row8
                                                                    let cf34
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r26
                                                                    match cf34
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr17 =>
                                                                    let r27 ←
                                                                    B.decode
                                                                    28#usize
                                                                    vr17
                                                                    0#usize
                                                                    let cf35
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r27
                                                                    match cf35
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val17 =>
                                                                    let
                                                                    boundary8
                                                                    ←
                                                                    B.boundary
                                                                    val17
                                                                    let b8 ←
                                                                    core.cmp.PartialEq.ne.trait_default
                                                                    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                    boundary8
                                                                    value7
                                                                    if b8
                                                                    then
                                                                    ok
                                                                    (core.result.Result.Err
                                                                    (r1_wire.Error.Boundary
                                                                    8#usize))
                                                                    else
                                                                    let cf36
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r26
                                                                    match cf36
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr18 =>
                                                                    let (r28,
                                                                    transcript9)
                                                                    ←
                                                                    r1_wire.SemanticTranscript.semantic_validated
                                                                    aspis_coreDigest32Inst
                                                                    transcript8
                                                                    vr18
                                                                    let cf37
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r28
                                                                    match cf37
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val18 =>
                                                                    let alpha9
                                                                    ←
                                                                    Array.update
                                                                    alpha8
                                                                    8#usize
                                                                    val18
                                                                    let value8
                                                                    ←
                                                                    B.value
                                                                    val17
                                                                    alpha9
                                                                    8#usize
                                                                    let i9 ←
                                                                    lift
                                                                    (UScalar.cast
                                                                    .U8
                                                                    9#usize)
                                                                    let row9
                                                                    ←
                                                                    15#u8 + i9
                                                                    let r29 ←
                                                                    r1_wire.Prefix.validated_record
                                                                    prefix1
                                                                    row9
                                                                    let cf38
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r29
                                                                    match cf38
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr19 =>
                                                                    let r30 ←
                                                                    B.decode
                                                                    28#usize
                                                                    vr19
                                                                    0#usize
                                                                    let cf39
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r30
                                                                    match cf39
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val19 =>
                                                                    let
                                                                    boundary9
                                                                    ←
                                                                    B.boundary
                                                                    val19
                                                                    let b9 ←
                                                                    core.cmp.PartialEq.ne.trait_default
                                                                    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                                                    boundary9
                                                                    value8
                                                                    if b9
                                                                    then
                                                                    ok
                                                                    (core.result.Result.Err
                                                                    (r1_wire.Error.Boundary
                                                                    9#usize))
                                                                    else
                                                                    let cf40
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r29
                                                                    match cf40
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    vr20 =>
                                                                    let (r31,
                                                                    transcript10)
                                                                    ←
                                                                    r1_wire.SemanticTranscript.semantic_validated
                                                                    aspis_coreDigest32Inst
                                                                    transcript9
                                                                    vr20
                                                                    let cf41
                                                                    ←
                                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                                    r31
                                                                    match cf41
                                                                    with
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Continue
                                                                    val20 =>
                                                                    let alpha10
                                                                    ←
                                                                    Array.update
                                                                    alpha9
                                                                    9#usize
                                                                    val20
                                                                    let value9
                                                                    ←
                                                                    B.value
                                                                    val19
                                                                    alpha10
                                                                    9#usize
                                                                    ok
                                                                    (core.result.Result.Ok
                                                                    (value9,
                                                                    alpha10,
                                                                    transcript10))
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                    |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                  |
                                                                    core.ops.control_flow.ControlFlow.Break
                                                                    residual =>
                                                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                                |
                                                                  core.ops.control_flow.ControlFlow.Break
                                                                  residual =>
                                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                    (aspis_core.field.QM31
                                                                    × (Array
                                                                    aspis_core.field.QM31
                                                                    10#usize)
                                                                    ×
                                                                    (r1_wire.SemanticTranscript
                                                                    H))
                                                                    (core.convert.FromSame
                                                                    r1_wire.Error)
                                                                    residual
                                                              |
                                                                core.ops.control_flow.ControlFlow.Break
                                                                residual =>
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                                  (aspis_core.field.QM31
                                                                  × (Array
                                                                  aspis_core.field.QM31
                                                                  10#usize) ×
                                                                  (r1_wire.SemanticTranscript
                                                                  H))
                                                                  (core.convert.FromSame
                                                                  r1_wire.Error)
                                                                  residual
                                                          |
                                                            core.ops.control_flow.ControlFlow.Break
                                                            residual =>
                                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                              (aspis_core.field.QM31
                                                              × (Array
                                                              aspis_core.field.QM31
                                                              10#usize) ×
                                                              (r1_wire.SemanticTranscript
                                                              H))
                                                              (core.convert.FromSame
                                                              r1_wire.Error)
                                                              residual
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                            (aspis_core.field.QM31
                                                            × (Array
                                                            aspis_core.field.QM31
                                                            10#usize) ×
                                                            (r1_wire.SemanticTranscript
                                                            H))
                                                            (core.convert.FromSame
                                                            r1_wire.Error)
                                                            residual
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                          (aspis_core.field.QM31
                                                          × (Array
                                                          aspis_core.field.QM31
                                                          10#usize) ×
                                                          (r1_wire.SemanticTranscript
                                                          H))
                                                          (core.convert.FromSame
                                                          r1_wire.Error)
                                                          residual
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                        (aspis_core.field.QM31
                                                        × (Array
                                                        aspis_core.field.QM31
                                                        10#usize) ×
                                                        (r1_wire.SemanticTranscript
                                                        H))
                                                        (core.convert.FromSame
                                                        r1_wire.Error) residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    (aspis_core.field.QM31 ×
                                                    (Array
                                                    aspis_core.field.QM31
                                                    10#usize) ×
                                                    (r1_wire.SemanticTranscript
                                                    H)) (core.convert.FromSame
                                                    r1_wire.Error) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  (aspis_core.field.QM31 ×
                                                  (Array aspis_core.field.QM31
                                                  10#usize) ×
                                                  (r1_wire.SemanticTranscript
                                                  H)) (core.convert.FromSame
                                                  r1_wire.Error) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (aspis_core.field.QM31 ×
                                                (Array aspis_core.field.QM31
                                                10#usize) ×
                                                (r1_wire.SemanticTranscript H))
                                                (core.convert.FromSame
                                                r1_wire.Error) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (aspis_core.field.QM31 × (Array
                                              aspis_core.field.QM31 10#usize)
                                              × (r1_wire.SemanticTranscript
                                              H)) (core.convert.FromSame
                                              r1_wire.Error) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (aspis_core.field.QM31 × (Array
                                          aspis_core.field.QM31 10#usize) ×
                                          (r1_wire.SemanticTranscript H))
                                          (core.convert.FromSame r1_wire.Error)
                                          residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (aspis_core.field.QM31 × (Array
                                        aspis_core.field.QM31 10#usize) ×
                                        (r1_wire.SemanticTranscript H))
                                        (core.convert.FromSame r1_wire.Error)
                                        residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (aspis_core.field.QM31 × (Array
                                      aspis_core.field.QM31 10#usize) ×
                                      (r1_wire.SemanticTranscript H))
                                      (core.convert.FromSame r1_wire.Error)
                                      residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (aspis_core.field.QM31 × (Array
                                    aspis_core.field.QM31 10#usize) ×
                                    (r1_wire.SemanticTranscript H))
                                    (core.convert.FromSame r1_wire.Error)
                                    residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (aspis_core.field.QM31 × (Array
                                aspis_core.field.QM31 10#usize) ×
                                (r1_wire.SemanticTranscript H))
                                (core.convert.FromSame r1_wire.Error) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (aspis_core.field.QM31 × (Array
                              aspis_core.field.QM31 10#usize) ×
                              (r1_wire.SemanticTranscript H))
                              (core.convert.FromSame r1_wire.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (aspis_core.field.QM31 × (Array
                            aspis_core.field.QM31 10#usize) ×
                            (r1_wire.SemanticTranscript H))
                            (core.convert.FromSame r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (aspis_core.field.QM31 × (Array
                          aspis_core.field.QM31 10#usize) ×
                          (r1_wire.SemanticTranscript H))
                          (core.convert.FromSame r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                      10#usize) × (r1_wire.SemanticTranscript H))
                      (core.convert.FromSame r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                    10#usize) × (r1_wire.SemanticTranscript H))
                    (core.convert.FromSame r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                  10#usize) × (r1_wire.SemanticTranscript H))
                  (core.convert.FromSame r1_wire.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (aspis_core.field.QM31 × (Array aspis_core.field.QM31
                10#usize) × (r1_wire.SemanticTranscript H))
                (core.convert.FromSame r1_wire.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
            (r1_wire.SemanticTranscript H)) (core.convert.FromSame
            r1_wire.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
          (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
        (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 10#usize) ×
      (r1_wire.SemanticTranscript H)) (core.convert.FromSame r1_wire.Error)
      residual

def RoundModel.entry (B : RoundModel.Boundaries)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 10#usize) × (r1_wire.SemanticTranscript H))
    r1_wire.Error)
  := do
  RoundModel.rounds B aspis_coreDigest32Inst prefix1 transcript

#print axioms RoundModel.rounds
#print axioms RoundModel.entry
end AspisR1PublicPreparation
