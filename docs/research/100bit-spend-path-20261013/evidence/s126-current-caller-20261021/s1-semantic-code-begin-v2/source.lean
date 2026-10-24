import S1SemanticCodeSemanticValidatedV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

def begin13_native {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
  (val val1 val2 val12 : aspis_core.field.QM31)
  (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Result ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r26 ←
    r1_wire.Prefix.validated_record
      prefix1 13#u8
  let cf26 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r26
  match cf26 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr13 =>
    let (r27, transcript14)
      ←
      r1_wire.SemanticTranscript.semantic_validated
        aspis_coreDigest32Inst
        transcript13 vr13
    let cf27 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r27
    match cf27 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val13 =>
      let r28 ←
        r1_wire.Prefix.validated_record
          prefix1 14#u8
      let cf28 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r28
      match cf28 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr14 =>
        let (r29,
          transcript15) ←
          r1_wire.SemanticTranscript.semantic_validated
            aspis_coreDigest32Inst
            transcript14
            vr14
        let cf29 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r29
        match cf29 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val14 =>
          let zc10 :=
            index_mut_back9
              val12
          ok
            (core.result.Result.Ok
            {
              lambda := val,
              chi := val1,
              theta := val2,
              zc := zc10,
              mu := val13,
              eta := val14
            },
            transcript15)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r30 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error)
              residual
          ok (r30,
            transcript15)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r29 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error)
            residual
        ok (r29,
          transcript14)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r28 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error)
          residual
      ok (r28,
        transcript14)
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    let r27 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error)
        residual
    ok (r27, transcript13)

def begin9_native {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
  (val val1 val2 val8 : aspis_core.field.QM31)
  (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Result ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r18 ←
    r1_wire.Prefix.validated_record prefix1
      9#u8
  let cf18 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r18
  match cf18 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr9 =>
    let (r19, transcript10) ←
      r1_wire.SemanticTranscript.semantic_validated
        aspis_coreDigest32Inst transcript9
        vr9
    let cf19 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r19
    match cf19 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val9 =>
      let zc6 := index_mut_back5 val8
      let (_, index_mut_back6) ←
        Array.index_mut_usize zc6 6#usize
      let r20 ←
        r1_wire.Prefix.validated_record
          prefix1 10#u8
      let cf20 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r20
      match cf20 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr10 =>
        let (r21, transcript11) ←
          r1_wire.SemanticTranscript.semantic_validated
            aspis_coreDigest32Inst
            transcript10 vr10
        let cf21 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r21
        match cf21 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val10 =>
          let zc7 := index_mut_back6 val9
          let (_, index_mut_back7) ←
            Array.index_mut_usize zc7
              7#usize
          let r22 ←
            r1_wire.Prefix.validated_record
              prefix1 11#u8
          let cf22 ←
            core.result.Result.Insts.CoreOpsTry.branch
              r22
          match cf22 with
          |
            core.ops.control_flow.ControlFlow.Continue
            vr11 =>
            let (r23, transcript12) ←
              r1_wire.SemanticTranscript.semantic_validated
                aspis_coreDigest32Inst
                transcript11 vr11
            let cf23 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r23
            match cf23 with
            |
              core.ops.control_flow.ControlFlow.Continue
              val11 =>
              let zc8 :=
                index_mut_back7 val10
              let (_, index_mut_back8) ←
                Array.index_mut_usize zc8
                  8#usize
              let r24 ←
                r1_wire.Prefix.validated_record
                  prefix1 12#u8
              let cf24 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r24
              match cf24 with
              |
                core.ops.control_flow.ControlFlow.Continue
                vr12 =>
                let (r25, transcript13) ←
                  r1_wire.SemanticTranscript.semantic_validated
                    aspis_coreDigest32Inst
                    transcript12 vr12
                let cf25 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r25
                match cf25 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val12 =>
                  let zc9 :=
                    index_mut_back8 val11
                  let (_, index_mut_back9)
                    ←
                    Array.index_mut_usize
                      zc9 9#usize
                  begin13_native aspis_coreDigest32Inst prefix1 transcript13 val val1 val2 val12 index_mut_back9
                |
                  core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r26 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame
                      r1_wire.Error)
                      residual
                  ok (r26, transcript13)
              |
                core.ops.control_flow.ControlFlow.Break
                residual =>
                let r25 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame
                    r1_wire.Error) residual
                ok (r25, transcript12)
            |
              core.ops.control_flow.ControlFlow.Break
              residual =>
              let r24 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges
                  (core.convert.FromSame
                  r1_wire.Error) residual
              ok (r24, transcript12)
          |
            core.ops.control_flow.ControlFlow.Break
            residual =>
            let r23 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges
                (core.convert.FromSame
                r1_wire.Error) residual
            ok (r23, transcript11)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r22 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error) residual
          ok (r22, transcript11)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r21 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error) residual
        ok (r21, transcript10)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r20 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error) residual
      ok (r20, transcript10)
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    let r19 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error) residual
    ok (r19, transcript9)

def begin5_native {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
  (val val1 val2 val4 : aspis_core.field.QM31)
  (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Result ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r10 ← r1_wire.Prefix.validated_record prefix1 5#u8
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue vr5 =>
    let (r11, transcript6) ←
      r1_wire.SemanticTranscript.semantic_validated
        aspis_coreDigest32Inst transcript5 vr5
    let cf11 ←
      core.result.Result.Insts.CoreOpsTry.branch r11
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val5 =>
      let zc2 := index_mut_back1 val4
      let (_, index_mut_back2) ←
        Array.index_mut_usize zc2 2#usize
      let r12 ←
        r1_wire.Prefix.validated_record prefix1 6#u8
      let cf12 ←
        core.result.Result.Insts.CoreOpsTry.branch r12
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue vr6 =>
        let (r13, transcript7) ←
          r1_wire.SemanticTranscript.semantic_validated
            aspis_coreDigest32Inst transcript6 vr6
        let cf13 ←
          core.result.Result.Insts.CoreOpsTry.branch r13
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val6
          =>
          let zc3 := index_mut_back2 val5
          let (_, index_mut_back3) ←
            Array.index_mut_usize zc3 3#usize
          let r14 ←
            r1_wire.Prefix.validated_record prefix1 7#u8
          let cf14 ←
            core.result.Result.Insts.CoreOpsTry.branch r14
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue vr7
            =>
            let (r15, transcript8) ←
              r1_wire.SemanticTranscript.semantic_validated
                aspis_coreDigest32Inst transcript7 vr7
            let cf15 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r15
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue
              val7 =>
              let zc4 := index_mut_back3 val6
              let (_, index_mut_back4) ←
                Array.index_mut_usize zc4 4#usize
              let r16 ←
                r1_wire.Prefix.validated_record prefix1
                  8#u8
              let cf16 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r16
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue
                vr8 =>
                let (r17, transcript9) ←
                  r1_wire.SemanticTranscript.semantic_validated
                    aspis_coreDigest32Inst transcript8 vr8
                let cf17 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r17
                match cf17 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val8 =>
                  let zc5 := index_mut_back4 val7
                  let (_, index_mut_back5) ←
                    Array.index_mut_usize zc5 5#usize
                  begin9_native aspis_coreDigest32Inst prefix1 transcript9 val val1 val2 val8 index_mut_back5
                | core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r18 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame r1_wire.Error)
                      residual
                  ok (r18, transcript9)
              | core.ops.control_flow.ControlFlow.Break
                residual =>
                let r17 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame r1_wire.Error)
                    residual
                ok (r17, transcript8)
            | core.ops.control_flow.ControlFlow.Break
              residual =>
              let r16 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame
                  r1_wire.Error) residual
              ok (r16, transcript8)
          | core.ops.control_flow.ControlFlow.Break
            residual =>
            let r15 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame
                r1_wire.Error) residual
            ok (r15, transcript7)
        | core.ops.control_flow.ControlFlow.Break residual
          =>
          let r14 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame
              r1_wire.Error) residual
          ok (r14, transcript7)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r13 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame
            r1_wire.Error) residual
        ok (r13, transcript6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r12 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame
          r1_wire.Error) residual
      ok (r12, transcript6)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r11 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame
        r1_wire.Error) residual
    ok (r11, transcript5)

def begin_native
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Result ((core.result.Result r1_wire.Challenges r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 0#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let (r1, transcript1) ←
      r1_wire.SemanticTranscript.semantic_validated aspis_coreDigest32Inst
        transcript vr
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.Prefix.validated_record prefix1 1#u8
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue vr1 =>
        let (r3, transcript2) ←
          r1_wire.SemanticTranscript.semantic_validated aspis_coreDigest32Inst
            transcript1 vr1
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let r4 ← r1_wire.Prefix.validated_record prefix1 2#u8
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue vr2 =>
            let (r5, transcript3) ←
              r1_wire.SemanticTranscript.semantic_validated
                aspis_coreDigest32Inst transcript2 vr2
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let zc := Array.repeat 10#usize aspis_core.field.QM31.ZERO
              let r6 ← r1_wire.Prefix.validated_record prefix1 3#u8
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue vr3 =>
                let (r7, transcript4) ←
                  r1_wire.SemanticTranscript.semantic_validated
                    aspis_coreDigest32Inst transcript3 vr3
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let (_, index_mut_back) ← Array.index_mut_usize zc 0#usize
                  let r8 ← r1_wire.Prefix.validated_record prefix1 4#u8
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue vr4 =>
                    let (r9, transcript5) ←
                      r1_wire.SemanticTranscript.semantic_validated
                        aspis_coreDigest32Inst transcript4 vr4
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let zc1 := index_mut_back val3
                      let (_, index_mut_back1) ←
                        Array.index_mut_usize zc1 1#usize
                      begin5_native aspis_coreDigest32Inst prefix1 transcript5 val val1 val2 val4 index_mut_back1
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r10 ←
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          r1_wire.Challenges (core.convert.FromSame
                          r1_wire.Error) residual
                      ok (r10, transcript5)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r9 ←
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        r1_wire.Challenges (core.convert.FromSame
                        r1_wire.Error) residual
                    ok (r9, transcript4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r8 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                      residual
                  ok (r8, transcript4)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                    residual
                ok (r7, transcript3)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                  residual
              ok (r6, transcript3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                residual
            ok (r5, transcript2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
          ok (r4, transcript2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
        ok (r3, transcript1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
      ok (r2, transcript1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
    ok (r1, transcript)

def begin13 {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
  (val val1 val2 val12 : aspis_core.field.QM31)
  (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r26 ←
    r1_wire.Prefix.validated_record
      prefix1 13#u8
  let cf26 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r26
  match cf26 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr13 =>
    let (r27, transcript14)
      ←
      semanticValidated
        aspis_coreDigest32Inst
        transcript13 vr13
    let cf27 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r27
    match cf27 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val13 =>
      let r28 ←
        r1_wire.Prefix.validated_record
          prefix1 14#u8
      let cf28 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r28
      match cf28 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr14 =>
        let (r29,
          transcript15) ←
          semanticValidated
            aspis_coreDigest32Inst
            transcript14
            vr14
        let cf29 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r29
        match cf29 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val14 =>
          let zc10 :=
            index_mut_back9
              val12
          pure
            (core.result.Result.Ok
            {
              lambda := val,
              chi := val1,
              theta := val2,
              zc := zc10,
              mu := val13,
              eta := val14
            },
            transcript15)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r30 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error)
              residual
          pure (r30,
            transcript15)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r29 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error)
            residual
        pure (r29,
          transcript14)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r28 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error)
          residual
      pure (r28,
        transcript14)
  |
    core.ops.control_flow.ControlFlow.Break
    residual =>
    let r27 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error)
        residual
    pure (r27, transcript13)

def begin9 {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
  (val val1 val2 val8 : aspis_core.field.QM31)
  (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r18 ←
    r1_wire.Prefix.validated_record prefix1
      9#u8
  let cf18 ←
    core.result.Result.Insts.CoreOpsTry.branch
      r18
  match cf18 with
  |
    core.ops.control_flow.ControlFlow.Continue
    vr9 =>
    let (r19, transcript10) ←
      semanticValidated
        aspis_coreDigest32Inst transcript9
        vr9
    let cf19 ←
      core.result.Result.Insts.CoreOpsTry.branch
        r19
    match cf19 with
    |
      core.ops.control_flow.ControlFlow.Continue
      val9 =>
      let zc6 := index_mut_back5 val8
      let (_, index_mut_back6) ←
        Array.index_mut_usize zc6 6#usize
      let r20 ←
        r1_wire.Prefix.validated_record
          prefix1 10#u8
      let cf20 ←
        core.result.Result.Insts.CoreOpsTry.branch
          r20
      match cf20 with
      |
        core.ops.control_flow.ControlFlow.Continue
        vr10 =>
        let (r21, transcript11) ←
          semanticValidated
            aspis_coreDigest32Inst
            transcript10 vr10
        let cf21 ←
          core.result.Result.Insts.CoreOpsTry.branch
            r21
        match cf21 with
        |
          core.ops.control_flow.ControlFlow.Continue
          val10 =>
          let zc7 := index_mut_back6 val9
          let (_, index_mut_back7) ←
            Array.index_mut_usize zc7
              7#usize
          let r22 ←
            r1_wire.Prefix.validated_record
              prefix1 11#u8
          let cf22 ←
            core.result.Result.Insts.CoreOpsTry.branch
              r22
          match cf22 with
          |
            core.ops.control_flow.ControlFlow.Continue
            vr11 =>
            let (r23, transcript12) ←
              semanticValidated
                aspis_coreDigest32Inst
                transcript11 vr11
            let cf23 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r23
            match cf23 with
            |
              core.ops.control_flow.ControlFlow.Continue
              val11 =>
              let zc8 :=
                index_mut_back7 val10
              let (_, index_mut_back8) ←
                Array.index_mut_usize zc8
                  8#usize
              let r24 ←
                r1_wire.Prefix.validated_record
                  prefix1 12#u8
              let cf24 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r24
              match cf24 with
              |
                core.ops.control_flow.ControlFlow.Continue
                vr12 =>
                let (r25, transcript13) ←
                  semanticValidated
                    aspis_coreDigest32Inst
                    transcript12 vr12
                let cf25 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r25
                match cf25 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val12 =>
                  let zc9 :=
                    index_mut_back8 val11
                  let (_, index_mut_back9)
                    ←
                    Array.index_mut_usize
                      zc9 9#usize
                  begin13 aspis_coreDigest32Inst prefix1 transcript13 val val1 val2 val12 index_mut_back9
                |
                  core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r26 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame
                      r1_wire.Error)
                      residual
                  pure (r26, transcript13)
              |
                core.ops.control_flow.ControlFlow.Break
                residual =>
                let r25 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame
                    r1_wire.Error) residual
                pure (r25, transcript12)
            |
              core.ops.control_flow.ControlFlow.Break
              residual =>
              let r24 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges
                  (core.convert.FromSame
                  r1_wire.Error) residual
              pure (r24, transcript12)
          |
            core.ops.control_flow.ControlFlow.Break
            residual =>
            let r23 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges
                (core.convert.FromSame
                r1_wire.Error) residual
            pure (r23, transcript11)
        |
          core.ops.control_flow.ControlFlow.Break
          residual =>
          let r22 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges
              (core.convert.FromSame
              r1_wire.Error) residual
          pure (r22, transcript11)
      |
        core.ops.control_flow.ControlFlow.Break
        residual =>
        let r21 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges
            (core.convert.FromSame
            r1_wire.Error) residual
        pure (r21, transcript10)
    |
      core.ops.control_flow.ControlFlow.Break
      residual =>
      let r20 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges
          (core.convert.FromSame
          r1_wire.Error) residual
      pure (r20, transcript10)
  | core.ops.control_flow.ControlFlow.Break
    residual =>
    let r19 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges
        (core.convert.FromSame
        r1_wire.Error) residual
    pure (r19, transcript9)

def begin5 {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
  (val val1 val2 val4 : aspis_core.field.QM31)
  (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  := do
  let r10 ← r1_wire.Prefix.validated_record prefix1 5#u8
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue vr5 =>
    let (r11, transcript6) ←
      semanticValidated
        aspis_coreDigest32Inst transcript5 vr5
    let cf11 ←
      core.result.Result.Insts.CoreOpsTry.branch r11
    match cf11 with
    | core.ops.control_flow.ControlFlow.Continue val5 =>
      let zc2 := index_mut_back1 val4
      let (_, index_mut_back2) ←
        Array.index_mut_usize zc2 2#usize
      let r12 ←
        r1_wire.Prefix.validated_record prefix1 6#u8
      let cf12 ←
        core.result.Result.Insts.CoreOpsTry.branch r12
      match cf12 with
      | core.ops.control_flow.ControlFlow.Continue vr6 =>
        let (r13, transcript7) ←
          semanticValidated
            aspis_coreDigest32Inst transcript6 vr6
        let cf13 ←
          core.result.Result.Insts.CoreOpsTry.branch r13
        match cf13 with
        | core.ops.control_flow.ControlFlow.Continue val6
          =>
          let zc3 := index_mut_back2 val5
          let (_, index_mut_back3) ←
            Array.index_mut_usize zc3 3#usize
          let r14 ←
            r1_wire.Prefix.validated_record prefix1 7#u8
          let cf14 ←
            core.result.Result.Insts.CoreOpsTry.branch r14
          match cf14 with
          | core.ops.control_flow.ControlFlow.Continue vr7
            =>
            let (r15, transcript8) ←
              semanticValidated
                aspis_coreDigest32Inst transcript7 vr7
            let cf15 ←
              core.result.Result.Insts.CoreOpsTry.branch
                r15
            match cf15 with
            | core.ops.control_flow.ControlFlow.Continue
              val7 =>
              let zc4 := index_mut_back3 val6
              let (_, index_mut_back4) ←
                Array.index_mut_usize zc4 4#usize
              let r16 ←
                r1_wire.Prefix.validated_record prefix1
                  8#u8
              let cf16 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r16
              match cf16 with
              | core.ops.control_flow.ControlFlow.Continue
                vr8 =>
                let (r17, transcript9) ←
                  semanticValidated
                    aspis_coreDigest32Inst transcript8 vr8
                let cf17 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r17
                match cf17 with
                |
                  core.ops.control_flow.ControlFlow.Continue
                  val8 =>
                  let zc5 := index_mut_back4 val7
                  let (_, index_mut_back5) ←
                    Array.index_mut_usize zc5 5#usize
                  begin9 aspis_coreDigest32Inst prefix1 transcript9 val val1 val2 val8 index_mut_back5
                | core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r18 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges
                      (core.convert.FromSame r1_wire.Error)
                      residual
                  pure (r18, transcript9)
              | core.ops.control_flow.ControlFlow.Break
                residual =>
                let r17 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges
                    (core.convert.FromSame r1_wire.Error)
                    residual
                pure (r17, transcript8)
            | core.ops.control_flow.ControlFlow.Break
              residual =>
              let r16 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame
                  r1_wire.Error) residual
              pure (r16, transcript8)
          | core.ops.control_flow.ControlFlow.Break
            residual =>
            let r15 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame
                r1_wire.Error) residual
            pure (r15, transcript7)
        | core.ops.control_flow.ControlFlow.Break residual
          =>
          let r14 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame
              r1_wire.Error) residual
          pure (r14, transcript7)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r13 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame
            r1_wire.Error) residual
        pure (r13, transcript6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r12 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame
          r1_wire.Error) residual
      pure (r12, transcript6)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r11 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame
        r1_wire.Error) residual
    pure (r11, transcript5)

def begin
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
  Code ((core.result.Result r1_wire.Challenges r1_wire.Error) ×
    (r1_wire.SemanticTranscript H))
  := do
  let r ← r1_wire.Prefix.validated_record prefix1 0#u8
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    let (r1, transcript1) ←
      semanticValidated aspis_coreDigest32Inst
        transcript vr
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← r1_wire.Prefix.validated_record prefix1 1#u8
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue vr1 =>
        let (r3, transcript2) ←
          semanticValidated aspis_coreDigest32Inst
            transcript1 vr1
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let r4 ← r1_wire.Prefix.validated_record prefix1 2#u8
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue vr2 =>
            let (r5, transcript3) ←
              semanticValidated
                aspis_coreDigest32Inst transcript2 vr2
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let zc := Array.repeat 10#usize aspis_core.field.QM31.ZERO
              let r6 ← r1_wire.Prefix.validated_record prefix1 3#u8
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue vr3 =>
                let (r7, transcript4) ←
                  semanticValidated
                    aspis_coreDigest32Inst transcript3 vr3
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let (_, index_mut_back) ← Array.index_mut_usize zc 0#usize
                  let r8 ← r1_wire.Prefix.validated_record prefix1 4#u8
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue vr4 =>
                    let (r9, transcript5) ←
                      semanticValidated
                        aspis_coreDigest32Inst transcript4 vr4
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let zc1 := index_mut_back val3
                      let (_, index_mut_back1) ←
                        Array.index_mut_usize zc1 1#usize
                      begin5 aspis_coreDigest32Inst prefix1 transcript5 val val1 val2 val4 index_mut_back1
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      let r10 ←
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          r1_wire.Challenges (core.convert.FromSame
                          r1_wire.Error) residual
                      pure (r10, transcript5)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r9 ←
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        r1_wire.Challenges (core.convert.FromSame
                        r1_wire.Error) residual
                    pure (r9, transcript4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r8 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                      residual
                  pure (r8, transcript4)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                    residual
                pure (r7, transcript3)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                  residual
              pure (r6, transcript3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                r1_wire.Challenges (core.convert.FromSame r1_wire.Error)
                residual
            pure (r5, transcript2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
          pure (r4, transcript2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
        pure (r3, transcript1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
      pure (r2, transcript1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        r1_wire.Challenges (core.convert.FromSame r1_wire.Error) residual
    pure (r1, transcript)

#print axioms begin13
#print axioms begin9
#print axioms begin5
#print axioms begin
end AspisR1PublicPreparation.S1SemanticCode
