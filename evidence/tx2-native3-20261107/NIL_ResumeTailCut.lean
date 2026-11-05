import NIL_ResumePrefixCut
set_option autoImplicit false
noncomputable section
namespace NIL_ResumeTailCut
open Aeneas Aeneas.Std Result ControlFlow Error NID_ResumeEmission
variable (NIL_call_0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NIL_call_1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NIL_call_2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F))

variable (NIL_call_3 : ∀ {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBoolInst :
  core.ops.function.FnMut F T Bool),
(core.slice.iter.Iter T) → F → Result (Bool × (core.slice.iter.Iter T)))

variable (NIL_call_4 : (Slice Std.U8) → Result (Option aspis_core.field.wide_exact.WideExact))

variable (NIL_call_5 : aspis_core.field.QM31 → Result aspis_core.field.QM31)

variable (NIL_call_6 : Result aspis_core.field.QM31)

variable (NIL_call_7 : ∀ {T : Type} (coremarkerCopyInst : core.marker.Copy T),
Std.Usize → T → Result (core.result.Result (alloc.vec.Vec T)
    aspis_core.r0.Error))

variable (NIL_call_8 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
(Slice Std.U8) → verifier.Prepared → (Array Std.U8 32#usize) →
    Std.Usize → H → Result (core.result.Result Unit verifier.Error))

variable (NIL_call_9 : (Slice Std.U8) → verifier.Prepared → verifier.Accumulator → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → (Option (verifier.Phase
    → Result Unit)) → verifier.QueryGeometry → verifier.BatchedWeights
    → Std.Usize → Result (core.result.Result (verifier.Accumulator ×
    verifier.BatchedWeights) verifier.Error))

variable (NIL_call_10 : ∀ (N : Std.Usize),
aspis_core.field.wide_exact.WideExact → Result (Array
    aspis_core.field.wide_exact.WideExact N))

variable (NIL_call_11 : (Slice Std.U8) → Std.Usize → Result (core.result.Result ((Array
    aspis_core.field.QM31 10#usize) × Std.Usize) verifier.Error))

variable (NIL_call_12 : (Slice Std.U8) → Std.Usize → (alloc.vec.Vec aspis_core.field.QM31) →
    Result (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) ×
    Std.Usize) verifier.Error))

variable (NIL_call_13 : (Array Std.U32 22#usize) → Result (core.result.Result Unit verifier.Error))

variable (NIL_call_14 : verifier.Reader → Result ((core.result.Result aspis_core.field.QM31
    verifier.Error) × verifier.Reader))

variable (NIL_call_15 : verifier.Reader → Result ((core.result.Result
    aspis_core.field.wide_exact.WideExact verifier.Error) × verifier.Reader))

variable (NIL_call_16 : ∀ (N : Std.Usize),
verifier.Reader → Result ((Array Std.U8 N) × verifier.Reader))

variable (NIL_call_17 : transport.Variant → Result Std.Usize)

variable (NIL_call_18 : transport.Variant → Result Std.Usize)

variable (NIL_call_19 : transport.Variant → Result Std.U8)

variable (NIL_call_20 : verifier.View → verifier.Prepared → verifier.Accumulator → (Option
    (verifier.Phase → Result Unit)) → Result (core.result.Result Unit
    verifier.Error))

variable (NIL_call_21 : verifier.BatchedWeights → (Slice aspis_core.field.QM31) → Result (Slice
    aspis_core.field.QM31))

variable (NIL_call_22 : (Slice aspis_core.field.QM31) → Result (core.result.Result
    verifier.BatchedWeights verifier.Error))

variable (NIL_call_23 : (Array Std.U32 22#usize) → Std.Usize → Std.Usize → Result
    (core.result.Result verifier.QueryGeometry verifier.Error))

variable (NIL_call_24 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit)


def tail {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let (state, r) ←
    NIL_call_16 32#usize
      { bytes, «at» := 80#usize }
  let (a3, r1) ← NIL_call_16 32#usize r
  let (a4, r2) ← NIL_call_16 32#usize r1
  let (r3, r4) ← NIL_call_15 r2
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (r5, r6) ← NIL_call_15 r4
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r7, r8) ← NIL_call_15 r6
      let cf2 ←
        core.result.Result.Insts.CoreOpsTry.branch r7
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r9, r10) ← NIL_call_15 r8
        let cf3 ←
          core.result.Result.Insts.CoreOpsTry.branch r9
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let (r11, r12) ← NIL_call_14 r10
          let cf4 ←
            core.result.Result.Insts.CoreOpsTry.branch r11
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4
            =>
            let (a5, r13) ← NIL_call_16 4#usize r12
            let i8 ← lift (core.num.U32.from_le_bytes a5)
            let (a6, r14) ← NIL_call_16 4#usize r13
            let i9 ← lift (core.num.U32.from_le_bytes a6)
            let (a7, r15) ← NIL_call_16 4#usize r14
            let i10 ← lift (core.num.U32.from_le_bytes a7)
            let (a8, r16) ← NIL_call_16 4#usize r15
            let i11 ← lift (core.num.U32.from_le_bytes a8)
            let (a9, r17) ← NIL_call_16 4#usize r16
            let i12 ← lift (core.num.U32.from_le_bytes a9)
            let (a10, r18) ←
              NIL_call_16 4#usize r17
            let i13 ← lift (core.num.U32.from_le_bytes a10)
            let (a11, r19) ←
              NIL_call_16 4#usize r18
            let i14 ← lift (core.num.U32.from_le_bytes a11)
            let (a12, r20) ←
              NIL_call_16 4#usize r19
            let i15 ← lift (core.num.U32.from_le_bytes a12)
            let (a13, r21) ←
              NIL_call_16 4#usize r20
            let i16 ← lift (core.num.U32.from_le_bytes a13)
            let (a14, r22) ←
              NIL_call_16 4#usize r21
            let i17 ← lift (core.num.U32.from_le_bytes a14)
            let (a15, r23) ←
              NIL_call_16 4#usize r22
            let i18 ← lift (core.num.U32.from_le_bytes a15)
            let (a16, r24) ←
              NIL_call_16 4#usize r23
            let i19 ← lift (core.num.U32.from_le_bytes a16)
            let (a17, r25) ←
              NIL_call_16 4#usize r24
            let i20 ← lift (core.num.U32.from_le_bytes a17)
            let (a18, r26) ←
              NIL_call_16 4#usize r25
            let i21 ← lift (core.num.U32.from_le_bytes a18)
            let (a19, r27) ←
              NIL_call_16 4#usize r26
            let i22 ← lift (core.num.U32.from_le_bytes a19)
            let (a20, r28) ←
              NIL_call_16 4#usize r27
            let i23 ← lift (core.num.U32.from_le_bytes a20)
            let (a21, r29) ←
              NIL_call_16 4#usize r28
            let i24 ← lift (core.num.U32.from_le_bytes a21)
            let (a22, r30) ←
              NIL_call_16 4#usize r29
            let i25 ← lift (core.num.U32.from_le_bytes a22)
            let (a23, r31) ←
              NIL_call_16 4#usize r30
            let i26 ← lift (core.num.U32.from_le_bytes a23)
            let (a24, r32) ←
              NIL_call_16 4#usize r31
            let i27 ← lift (core.num.U32.from_le_bytes a24)
            let (a25, r33) ←
              NIL_call_16 4#usize r32
            let i28 ← lift (core.num.U32.from_le_bytes a25)
            let (a26, r34) ←
              NIL_call_16 4#usize r33
            let i29 ← lift (core.num.U32.from_le_bytes a26)
            let r35 ←
              NIL_call_13
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
                NIL_call_11 bytes
                  r34.«at»
              let cf6 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r36
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue
                val5 =>
                let (semantic_alpha, at1) := val5
                let (r37, r38) ←
                  NIL_call_14
                    { r34 with «at» := at1 }
                let cf7 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r37
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue
                  val6 =>
                  let (r39, r40) ← NIL_call_14 r38
                  let cf8 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r39
                  match cf8 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    val7 =>
                    let (r41, r42) ← NIL_call_14 r40
                    let cf9 ←
                      core.result.Result.Insts.CoreOpsTry.branch
                        r41
                    match cf9 with
                    |
                      core.ops.control_flow.ControlFlow.Continue
                      val8 =>
                      let (r43, r44) ←
                        NIL_call_14 r42
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch
                          r43
                      match cf10 with
                      |
                        core.ops.control_flow.ControlFlow.Continue
                        val9 =>
                        let (r45, r46) ←
                          NIL_call_15 r44
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch
                            r45
                        match cf11 with
                        |
                          core.ops.control_flow.ControlFlow.Continue
                          val10 =>
                          let (r47, r48) ←
                            NIL_call_15 r46
                          let cf12 ←
                            core.result.Result.Insts.CoreOpsTry.branch
                              r47
                          match cf12 with
                          |
                            core.ops.control_flow.ControlFlow.Continue
                            val11 =>
                            let (r49, r50) ←
                              NIL_call_14 r48
                            let cf13 ←
                              core.result.Result.Insts.CoreOpsTry.branch
                                r49
                            match cf13 with
                            |
                              core.ops.control_flow.ControlFlow.Continue
                              val12 =>
                              let i30 ←
                                NIL_call_18 v
                              let q ←
                                NIL_call_6
                              let r51 ←
                                NIL_call_7
                                  (aspis_core.field.QM31.Insts.CoreMarkerCopy NIL_call_5)
                                  i30 q
                              let r52 ←
                                NIL_call_2
                                  (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
                                  aspis_coredigestDigest32Inst)
                                  r51 ()
                              let cf14 ←
                                core.result.Result.Insts.CoreOpsTry.branch
                                  r52
                              match cf14 with
                              |
                                core.ops.control_flow.ControlFlow.Continue
                                val13 =>
                                let r53 ←
                                  NIL_call_12
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

/-- [aspis_r1_cost_probe::compact::FINAL_LEN]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 45:0-45:32
    Visibility: public -/
@[global_simps, irreducible] def compact.FINAL_LEN : Std.Usize := 64#usize

/-- [aspis_r1_cost_probe::compact::HEADER]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 26:0-26:29
    Visibility: public -/
@[global_simps, irreducible] def compact.HEADER : Std.Usize := 16#usize

end NIL_ResumeTailCut
