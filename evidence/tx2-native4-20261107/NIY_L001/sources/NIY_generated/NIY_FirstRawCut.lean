import NIL_ResumeComposition
import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_FirstRawCut
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission

/-- Literal fresh suffix after the three raw32 calls; source is NIL_ResumeTailCut.tail.
No reply or reader is reselected. -/
def freshAfterRaw (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state a3 a4 : Array U8 32#usize) (r2 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let (r3, r4) ← NIL_FreshOps.readE r2
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r5, r6) ← NIL_FreshOps.readE r4
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r7, r8) ← NIL_FreshOps.readE r6
      let cf2 ←
        core.result.Result.Insts.CoreOpsTry.branch r7
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r9, r10) ← NIL_FreshOps.readE r8
        let cf3 ←
          core.result.Result.Insts.CoreOpsTry.branch r9
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let (r11, r12) ← NIL_FreshOps.readK r10
          let cf4 ←
            core.result.Result.Insts.CoreOpsTry.branch r11
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4
            =>
            let (a5, r13) ← NIL_FreshOps.raw 4#usize r12
            let i8 ← lift (core.num.U32.from_le_bytes a5)
            let (a6, r14) ← NIL_FreshOps.raw 4#usize r13
            let i9 ← lift (core.num.U32.from_le_bytes a6)
            let (a7, r15) ← NIL_FreshOps.raw 4#usize r14
            let i10 ← lift (core.num.U32.from_le_bytes a7)
            let (a8, r16) ← NIL_FreshOps.raw 4#usize r15
            let i11 ← lift (core.num.U32.from_le_bytes a8)
            let (a9, r17) ← NIL_FreshOps.raw 4#usize r16
            let i12 ← lift (core.num.U32.from_le_bytes a9)
            let (a10, r18) ←
              NIL_FreshOps.raw 4#usize r17
            let i13 ← lift (core.num.U32.from_le_bytes a10)
            let (a11, r19) ←
              NIL_FreshOps.raw 4#usize r18
            let i14 ← lift (core.num.U32.from_le_bytes a11)
            let (a12, r20) ←
              NIL_FreshOps.raw 4#usize r19
            let i15 ← lift (core.num.U32.from_le_bytes a12)
            let (a13, r21) ←
              NIL_FreshOps.raw 4#usize r20
            let i16 ← lift (core.num.U32.from_le_bytes a13)
            let (a14, r22) ←
              NIL_FreshOps.raw 4#usize r21
            let i17 ← lift (core.num.U32.from_le_bytes a14)
            let (a15, r23) ←
              NIL_FreshOps.raw 4#usize r22
            let i18 ← lift (core.num.U32.from_le_bytes a15)
            let (a16, r24) ←
              NIL_FreshOps.raw 4#usize r23
            let i19 ← lift (core.num.U32.from_le_bytes a16)
            let (a17, r25) ←
              NIL_FreshOps.raw 4#usize r24
            let i20 ← lift (core.num.U32.from_le_bytes a17)
            let (a18, r26) ←
              NIL_FreshOps.raw 4#usize r25
            let i21 ← lift (core.num.U32.from_le_bytes a18)
            let (a19, r27) ←
              NIL_FreshOps.raw 4#usize r26
            let i22 ← lift (core.num.U32.from_le_bytes a19)
            let (a20, r28) ←
              NIL_FreshOps.raw 4#usize r27
            let i23 ← lift (core.num.U32.from_le_bytes a20)
            let (a21, r29) ←
              NIL_FreshOps.raw 4#usize r28
            let i24 ← lift (core.num.U32.from_le_bytes a21)
            let (a22, r30) ←
              NIL_FreshOps.raw 4#usize r29
            let i25 ← lift (core.num.U32.from_le_bytes a22)
            let (a23, r31) ←
              NIL_FreshOps.raw 4#usize r30
            let i26 ← lift (core.num.U32.from_le_bytes a23)
            let (a24, r32) ←
              NIL_FreshOps.raw 4#usize r31
            let i27 ← lift (core.num.U32.from_le_bytes a24)
            let (a25, r33) ←
              NIL_FreshOps.raw 4#usize r32
            let i28 ← lift (core.num.U32.from_le_bytes a25)
            let (a26, r34) ←
              NIL_FreshOps.raw 4#usize r33
            let i29 ← lift (core.num.U32.from_le_bytes a26)
            let r35 ←
              NIL_FreshOps.validate
                (Array.make 22#usize [
                  i8, i9, i10, i11, i12, i13, i14, i15, i16,
                  i17, i18, i19, i20, i21, i22, i23, i24,
                  i25, i26, i27, i28, i29
                  ])
            let cf5 ←
              core.result.Result.Insts.CoreOpsTry.branch r35
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r36 ←
                NIL_FreshOps.semantic bytes
                  r34.«at»
              let cf6 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r36
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue
                val5 =>
                let (semantic_alpha, at1) := val5
                let (r37, r38) ←
                  NIL_FreshOps.readK
                    { r34 with «at» := at1 }
                let cf7 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r37
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue
                  val6 =>
                  let (r39, r40) ← NIL_FreshOps.readK r38
                  let cf8 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r39
                  match cf8 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    val7 =>
                    let (r41, r42) ← NIL_FreshOps.readK r40
                    let cf9 ←
                      core.result.Result.Insts.CoreOpsTry.branch
                        r41
                    match cf9 with
                    |
                      core.ops.control_flow.ControlFlow.Continue
                      val8 =>
                      let (r43, r44) ←
                        NIL_FreshOps.readK r42
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch
                          r43
                      match cf10 with
                      |
                        core.ops.control_flow.ControlFlow.Continue
                        val9 =>
                        let (r45, r46) ←
                          NIL_FreshOps.readE r44
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch
                            r45
                        match cf11 with
                        |
                          core.ops.control_flow.ControlFlow.Continue
                          val10 =>
                          let (r47, r48) ←
                            NIL_FreshOps.readE r46
                          let cf12 ←
                            core.result.Result.Insts.CoreOpsTry.branch
                              r47
                          match cf12 with
                          |
                            core.ops.control_flow.ControlFlow.Continue
                            val11 =>
                            let (r49, r50) ←
                              NIL_FreshOps.readK r48
                            let cf13 ←
                              core.result.Result.Insts.CoreOpsTry.branch
                                r49
                            match cf13 with
                            |
                              core.ops.control_flow.ControlFlow.Continue
                              val12 =>
                              let i30 ←
                                (fun v=>AspisR1.CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
                              let q ←
                                (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
                              let r51 ←
                                (NIL_FreshOps.filled reserved)
                                  (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x))
                                  i30 q
                              let r52 ←
                                NIL_FreshOps.mapError
                                  (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  (NIL_FreshOps.digest d))
                                  r51 ()
                              let cf14 ←
                                core.result.Result.Insts.CoreOpsTry.branch
                                  r52
                              match cf14 with
                              |
                                core.ops.control_flow.ControlFlow.Continue
                                val13 =>
                                let r53 ←
                                  NIL_FreshOps.weights
                                    bytes r50.«at» val13
                                let cf15 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r53
                                match cf15 with
                                |
                                  core.ops.control_flow.ControlFlow.Continue
                                  val14 =>
                                  let (weights, at2) := val14
                                  if at2 != end1
                                  then
                                    ok
                                      (core.result.Result.Err
                                      verifier.Error.Checkpoint)
                                  else
                                    let i31 ←
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
                                         queries :=
                                           (Array.make
                                              22#usize [
                                             i8, i9, i10,
                                             i11, i12, i13,
                                             i14, i15, i16,
                                             i17, i18, i19,
                                             i20, i21, i22,
                                             i23, i24, i25,
                                             i26, i27, i28,
                                             i29
                                             ]),
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
                                        next := i31
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


def fresh (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8) := do
 let (state,r) ← NIL_FreshOps.raw 32#usize {bytes, «at» := 80#usize}
 let (a3,r1) ← NIL_FreshOps.raw 32#usize r
 let (a4,r2) ← NIL_FreshOps.raw 32#usize r1
 freshAfterRaw reserved d bytes v end1 i4 state a3 a4 r2

theorem fresh_source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8) :
 NIL_ResumeSplit.tail reserved d bytes v end1 i4=fresh reserved d bytes v end1 i4 := by
 unfold NIL_ResumeSplit.tail NIL_ResumeTailCut.tail fresh
 apply NIL_ResultCases.bind_congr
 rintro ⟨state,r⟩
 apply NIL_ResultCases.bind_congr
 rintro ⟨a3,r1⟩
 apply NIL_ResultCases.bind_congr
 rintro ⟨a4,r2⟩
 rfl
#print axioms fresh_source
end NIY_FirstRawCut
