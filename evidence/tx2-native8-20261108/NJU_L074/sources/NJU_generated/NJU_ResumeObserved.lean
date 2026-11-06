import NJU_Log
import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeObserved
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)

/-- Full replies at actual entered resume sites. This is a source-log stage;
its native cut association must still be assembled and is not a root premise. -/
inductive Event where
 | digest (chunks : Slice (Slice U8)) (reply : Result (Array U8 32#usize))
 | headerAny (it : core.slice.iter.Iter U8) (reply : Result (Bool × core.slice.iter.Iter U8))
 | raw (n : Usize) (reader : verifier.Reader) (reply : Result (Array U8 n × verifier.Reader))
 | k (reader : verifier.Reader) (reply : Result (core.result.Result K verifier.Error × verifier.Reader))
 | e (reader : verifier.Reader) (reply : Result (core.result.Result E verifier.Error × verifier.Reader))
 | semantic (bytes : Slice U8) (cursor : Usize) (reply : R (Array K 10#usize × Usize))
 | weights (bytes : Slice U8) (cursor : Usize) (before : alloc.vec.Vec K)
   (reply : R (alloc.vec.Vec K × Usize))
 | validate (queries : Array U32 22#usize) (reply : R Unit)
 | filled (n : Usize) (value : K)
   (reply : Result (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error))

def run (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
  NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator)
    verifier.Error)
  := do
  let i := Slice.len bytes
  let i1 ← (fun v=>CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant v)) v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne ((Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← (fun v=>CheckpointBytes4Ops.tag (NIL_Carriers.variant v)) v
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
            let (b1, _) ←
              (fun inst it f=>NJU_Log.record (.headerAny it) (NIL_FreshOps.any inst it f))
                (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
                (NIL_FreshOps.digest d)) i6 ()
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← lift (Std.Usize.wrapping_sub i7 32#usize)
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize }
              let s3 ← lift (Array.to_slice (Array.make 1#usize [ proof ]))
              let a ← NJU_Log.record (.digest s3) ((NIL_FreshOps.digest d).digest hash s3)
              let b2 ←
                CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s2 a
              if b2
              then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize }
                let s5 ←
                  lift (Array.to_slice (Array.make 1#usize [ public1 ]))
                let a1 ← NJU_Log.record (.digest s5) ((NIL_FreshOps.digest d).digest hash s5)
                let b3 ←
                  CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s4
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
                  let a2 ← NJU_Log.record (.digest s9) ((NIL_FreshOps.digest d).digest hash s9)
                  let b4 ←
                    CheckpointBytes4Ops.ne core.cmp.PartialEqU8
                      s6 a2
                  if b4
                  then ok (core.result.Result.Err verifier.Error.Checkpoint)
                  else
                    let (state, r) ←
                      (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 32#usize
                        { bytes, «at» := 80#usize }
                    let (a3, r1) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 32#usize r
                    let (a4, r2) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 32#usize r1
                    let (r3, r4) ← (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r2
                    let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
                    match cf with
                    | core.ops.control_flow.ControlFlow.Continue val =>
                      let (r5, r6) ← (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r4
                      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
                      match cf1 with
                      | core.ops.control_flow.ControlFlow.Continue val1 =>
                        let (r7, r8) ← (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r6
                        let cf2 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf2 with
                        | core.ops.control_flow.ControlFlow.Continue val2 =>
                          let (r9, r10) ← (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r8
                          let cf3 ←
                            core.result.Result.Insts.CoreOpsTry.branch r9
                          match cf3 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let (r11, r12) ← (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)) r10
                            let cf4 ←
                              core.result.Result.Insts.CoreOpsTry.branch r11
                            match cf4 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let (a5, r13) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r12
                              let i8 ← lift (core.num.U32.from_le_bytes a5)
                              let (a6, r14) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r13
                              let i9 ← lift (core.num.U32.from_le_bytes a6)
                              let (a7, r15) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r14
                              let i10 ← lift (core.num.U32.from_le_bytes a7)
                              let (a8, r16) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r15
                              let i11 ← lift (core.num.U32.from_le_bytes a8)
                              let (a9, r17) ← (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r16
                              let i12 ← lift (core.num.U32.from_le_bytes a9)
                              let (a10, r18) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r17
                              let i13 ← lift (core.num.U32.from_le_bytes a10)
                              let (a11, r19) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r18
                              let i14 ← lift (core.num.U32.from_le_bytes a11)
                              let (a12, r20) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r19
                              let i15 ← lift (core.num.U32.from_le_bytes a12)
                              let (a13, r21) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r20
                              let i16 ← lift (core.num.U32.from_le_bytes a13)
                              let (a14, r22) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r21
                              let i17 ← lift (core.num.U32.from_le_bytes a14)
                              let (a15, r23) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r22
                              let i18 ← lift (core.num.U32.from_le_bytes a15)
                              let (a16, r24) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r23
                              let i19 ← lift (core.num.U32.from_le_bytes a16)
                              let (a17, r25) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r24
                              let i20 ← lift (core.num.U32.from_le_bytes a17)
                              let (a18, r26) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r25
                              let i21 ← lift (core.num.U32.from_le_bytes a18)
                              let (a19, r27) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r26
                              let i22 ← lift (core.num.U32.from_le_bytes a19)
                              let (a20, r28) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r27
                              let i23 ← lift (core.num.U32.from_le_bytes a20)
                              let (a21, r29) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r28
                              let i24 ← lift (core.num.U32.from_le_bytes a21)
                              let (a22, r30) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r29
                              let i25 ← lift (core.num.U32.from_le_bytes a22)
                              let (a23, r31) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r30
                              let i26 ← lift (core.num.U32.from_le_bytes a23)
                              let (a24, r32) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r31
                              let i27 ← lift (core.num.U32.from_le_bytes a24)
                              let (a25, r33) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r32
                              let i28 ← lift (core.num.U32.from_le_bytes a25)
                              let (a26, r34) ←
                                (fun n reader=>NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)) 4#usize r33
                              let i29 ← lift (core.num.U32.from_le_bytes a26)
                              let queryValues := (Array.make 22#usize [
                                    i8, i9, i10, i11, i12, i13, i14, i15, i16,
                                    i17, i18, i19, i20, i21, i22, i23, i24,
                                    i25, i26, i27, i28, i29
                                    ])
                              let r35 ←
                                (fun queries=>NJU_Log.record (.validate queries) (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries))
                                  queryValues
                              let cf5 ←
                                core.result.Result.Insts.CoreOpsTry.branch r35
                              match cf5 with
                              | core.ops.control_flow.ControlFlow.Continue _ =>
                                let r36 ←
                                  (fun bytes cursor=>NJU_Log.record (.semantic bytes cursor) (NIL_FreshOps.semantic bytes cursor)) bytes
                                    r34.«at»
                                let cf6 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r36
                                match cf6 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val5 =>
                                  let (semantic_alpha, at1) := val5
                                  let (r37, r38) ←
                                    (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader))
                                      { r34 with «at» := at1 }
                                  let cf7 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r37
                                  match cf7 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val6 =>
                                    let (r39, r40) ← (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)) r38
                                    let cf8 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r39
                                    match cf8 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val7 =>
                                      let (r41, r42) ← (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)) r40
                                      let cf9 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r41
                                      match cf9 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val8 =>
                                        let (r43, r44) ←
                                          (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)) r42
                                        let cf10 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r43
                                        match cf10 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val9 =>
                                          let (r45, r46) ←
                                            (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r44
                                          let cf11 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r45
                                          match cf11 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val10 =>
                                            let (r47, r48) ←
                                              (fun reader=>NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)) r46
                                            let cf12 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r47
                                            match cf12 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val11 =>
                                              let (r49, r50) ←
                                                (fun reader=>NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)) r48
                                              let cf13 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r49
                                              match cf13 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val12 =>
                                                let i30 ←
                                                  (fun v=>CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
                                                let q ←
                                                  (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
                                                let r51 ←
                                                  (fun copy n value=>NJU_Log.record (.filled n value) (NIL_FreshOps.filled (NJC_FilledClause.reserved reservation) copy n value))
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
                                                    (fun bytes cursor weights=>NJU_Log.record (.weights bytes cursor weights) (NIL_FreshOps.weights bytes cursor weights))
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
                                                             queryValues,
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

/-- Every branch is the SAME retained emitted resume invocation. This erasure
is source-only until all native cut assertions and complete internal loops
are attached; callback success and completed parent equality are not inputs. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 (run reservation d ck proof pub v hash).result=
 NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash := by
 unfold run NJC_RawCalls.resume NID_ResumeEmission.verifier.resume
 simp only [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,NJU_Log.erase_lift,NJU_Log.erase_pure]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value
    cases value with
    | Continue payload => cases payload
    | Break residual => skip)
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,
    NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,if_pos,if_neg])
 | split
 all_goals simp_all [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_liftM,
  NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases]

#print source
#print axioms source
end NJU_ResumeObserved
