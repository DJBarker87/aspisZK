import T2Nat_ReaderSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderFission
open Aeneas Aeneas.Std Result AspisR1Stage2
def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
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
                let r36 ←
                  ops.readSemanticAlpha bytes
                    r34.«at»
                let cf6 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r36
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue
                  val5 =>
                  let (semantic_alpha, at1) := val5
                  T2Nat_ReaderSuffix.source ops bytes v i4 end1 state a3 a4
                    val val1 val2 val3 val4 (Array.make 22#usize [ i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29 ]) semantic_alpha {r34 with «at» := at1}
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

theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    tail ops bytes v i4 end1 s6 a2 = Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2 := rfl

#print axioms source
end AspisR1.T2Nat_ReaderFission
end
