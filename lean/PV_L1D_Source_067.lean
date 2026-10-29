import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_043
import PV_L1D_Source_044
import PV_L1D_Source_045
import PV_L1D_Source_047
import PV_L1D_Source_049
import PV_L1D_Source_051
import PV_L1D_Source_052
import PV_L1D_Source_055
import PV_L1D_Source_056
import PV_L1D_Source_066
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_067
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H)
  (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
  (CommitmentsInst : host_semantic.Commitments T2)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1)
  (commitments : T2) (hash : H) (variant : transport.Variant) :
  Logged ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T2)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let r ← PV_L1D_Logged.lift (host_semantic.check_semantic_columns c1 d g)
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, commitments1) ← PV_L1D_Logged.lift (CommitmentsInst.c1 commitments c1 d)
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ← PV_L1D_Logged.lift (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
          public1)
      let r3 ← PV_L1D_Logged.lift (core.result.Result.map_err
          (host_semantic.build_with_helper_mode.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
          aspis_coredigestDigest32Inst
          coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
          CommitmentsInst) r2 ())
      let cf2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r3)
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s := alloc.vec.Vec.deref val1
        let r4 ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.new aspis_coredigestDigest32Inst hash s
            val)
        let cf3 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r4)
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice val))
          let bytes ← PV_L1D_Logged.lift (alloc.slice.Slice.to_vec core.clone.CloneU8 s1)
          let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
          let (r5, val3, bytes1) ←
            PV_L1D_Source_044.produce aspis_coredigestDigest32Inst 0#u8 s2
              val2 bytes
          let cf4 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r5)
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s3 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
            let (r6, val5, bytes2) ←
              PV_L1D_Source_044.produce aspis_coredigestDigest32Inst 1#u8 s3
                val3 bytes1
            let cf5 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r6)
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val6 =>
              let r7 ← PV_L1D_Logged.lift (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst.call_once
                  helper (val4, val6))
              let cf6 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r7)
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val7 =>
                let (s4, deref_mut_back) ← PV_L1D_Logged.lift (Aeneas.Std.lift (alloc.vec.Vec.deref_mut val7))
                let s5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice h1_padding))
                let (r8, s6) ← PV_L1D_Logged.lift (aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
                    s4 s5)
                let r9 ← PV_L1D_Logged.lift (core.result.Result.map_err
                    (host_semantic.build_with_helper_mode.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
                    aspis_coredigestDigest32Inst
                    coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
                    CommitmentsInst) r8 ())
                let cf7 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r9)
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let val8 := deref_mut_back s6
                  let i := alloc.vec.Vec.len val8
                  if i != 1024#usize
                  then
                    Pure.pure (core.result.Result.Err r1_wire.Error.Public,
                      commitments1)
                  else
                    let s7 := alloc.vec.Vec.deref val8
                    let o ← PV_L1D_Logged.lift (aspis_statement.state_only_semantic.state_only_copy_helper_sum
                        s7)
                    let q ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
                    let b ← PV_L1D_Logged.lift (core.cmp.PartialEq.ne.trait_default
                        (core.option.Option.Insts.CoreCmpPartialEqOption
                        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31) o
                        (some q))
                    if b
                    then
                      Pure.pure (core.result.Result.Err r1_wire.Error.Public,
                        commitments1)
                    else
                      let s8 := alloc.vec.Vec.deref val8
                      let (r10, commitments2) ← PV_L1D_Logged.lift (CommitmentsInst.c2 commitments1 s8 g)
                      let cf8 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r10)
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let s9 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice val9))
                        let (r11, val10, bytes3) ←
                          PV_L1D_Source_044.produce
                            aspis_coredigestDigest32Inst 2#u8 s9 val5 bytes2
                        let cf9 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r11)
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val11 =>
                          let (r12, val12, bytes4) ←
                            PV_L1D_Source_056.produce aspis_coredigestDigest32Inst
                              val10 bytes3
                          let cf10 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r12)
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val13 =>
                            let s10 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8)))
                            let (r13, val14, bytes5) ←
                              PV_L1D_Source_044.produce
                                aspis_coredigestDigest32Inst 13#u8 s10 val12
                                bytes4
                            let cf11 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r13)
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val15
                              =>
                              let columns ←
                                PV_L1D_Source_052.produce c1 val8 g d
                              let dc ← PV_L1D_Logged.lift (transport.Variant.coefficients
                                  aspis_core.field.QM31.Insts.CoreMarkerCopy
                                  variant d)
                              let mask_sum ←
                                PV_L1D_Source_051.produce columns
                              let mask_sum1 ←
                                PV_L1D_Source_055.produce mask_sum dc
                              let we ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.from_qm31
                                  mask_sum1)
                              let a ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.to_le_bytes
                                  we)
                              let s11 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a))
                              let (r14, val16, bytes6) ←
                                PV_L1D_Source_044.produce
                                  aspis_coredigestDigest32Inst 14#u8 s11 val14
                                  bytes5
                              let cf12 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r14)
                              match cf12 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val17 =>
                                let (r15, val18, bytes7) ←
                                  PV_L1D_Source_043.produce
                                    aspis_coredigestDigest32Inst
                                    host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
                                    val16 bytes6 mask_sum1
                                    {
                                      «public» := public1,
                                      columns,
                                      challenges :=
                                        {
                                          lambda := val4,
                                          chi := val6,
                                          theta := val11,
                                          zc := val13,
                                          mu := val15,
                                          eta := val17
                                        },
                                      eta := val17,
                                      d := dc
                                    }
                                let cf13 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                    r15)
                                match cf13 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val19 =>
                                  let (alpha, _) := val19
                                  let r16 ←
                                    PV_L1D_Source_066.produce columns alpha
                                  let cf14 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                      r16)
                                  match cf14 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val20 =>
                                    let state_before_z0 ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.impl.state
                                        aspis_coredigestDigest32Inst val18)
                                    let q1 ← PV_L1D_Logged.lift (Array.index_usize alpha 8#usize)
                                    let q2 ← PV_L1D_Logged.lift (Array.index_usize alpha 9#usize)
                                    let extras ←
                                      PV_L1D_Source_049.produce columns
                                        variant q1 q2
                                    let v ←
                                      PV_L1D_Source_047.produce val20 extras
                                    let s12 := alloc.vec.Vec.deref v
                                    let r17 ← PV_L1D_Logged.lift (host_wire.record 25#u8 s12)
                                    let cf15 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                        r17)
                                    match cf15 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val21 =>
                                      let s13 := alloc.vec.Vec.deref val21
                                      let (r18, val22) ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.challenge_reference_circle_point
                                          aspis_coredigestDigest32Inst val18
                                          25#u8 s13)
                                      let cf16 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                          r18)
                                      match cf16 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val23 =>
                                        let s14 := alloc.vec.Vec.deref val21
                                        let bytes8 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice
                                            core.clone.CloneU8 bytes7 s14)
                                        let v1 ←
                                          PV_L1D_Source_045.produce columns
                                            variant val23
                                        let s15 := alloc.vec.Vec.deref v1
                                        let r19 ← PV_L1D_Logged.lift (host_wire.record 26#u8 s15)
                                        let cf17 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                            r19)
                                        match cf17 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val24 =>
                                          let s16 := alloc.vec.Vec.deref val24
                                          let (r20, val25) ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.challenge_reference_circle_point
                                              aspis_coredigestDigest32Inst
                                              val22 26#u8 s16)
                                          let cf18 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch
                                              r20)
                                          match cf18 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val26 =>
                                            let s17 :=
                                              alloc.vec.Vec.deref val24
                                            let bytes9 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice
                                                core.clone.CloneU8 bytes8 s17)
                                            let b1 ← PV_L1D_Logged.lift (aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
                                                val23 val26)
                                            if b1
                                            then
                                              Pure.pure (core.result.Result.Err
                                                r1_wire.Error.EqualCirclePoints,
                                                commitments2)
                                            else
                                              Pure.pure (core.result.Result.Ok
                                                {
                                                  bytes := bytes9,
                                                  transcript := val25,
                                                  challenges :=
                                                    {
                                                      lambda := val4,
                                                      chi := val6,
                                                      theta := val11,
                                                      zc := val13,
                                                      mu := val15,
                                                      eta := val17
                                                    },
                                                  alpha,
                                                  state_before_z0,
                                                  roots :=
                                                    (Array.make 2#usize [
                                                      val, val9
                                                      ]),
                                                  columns,
                                                  z :=
                                                    (Array.make 2#usize [
                                                      val23, val26
                                                      ])
                                                }, commitments2)
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            let r21 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (host_semantic.BuiltSemantics
                                                H) (core.convert.FromSame
                                                r1_wire.Error) residual)
                                            Pure.pure (r21, commitments2)
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r20 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (host_semantic.BuiltSemantics H)
                                              (core.convert.FromSame
                                              r1_wire.Error) residual)
                                          Pure.pure (r20, commitments2)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r19 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            (host_semantic.BuiltSemantics H)
                                            (core.convert.FromSame
                                            r1_wire.Error) residual)
                                        Pure.pure (r19, commitments2)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r18 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (host_semantic.BuiltSemantics H)
                                          (core.convert.FromSame r1_wire.Error)
                                          residual)
                                      Pure.pure (r18, commitments2)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r17 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (host_semantic.BuiltSemantics H)
                                        (core.convert.FromSame r1_wire.Error)
                                        residual)
                                    Pure.pure (r17, commitments2)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (host_semantic.BuiltSemantics H)
                                      (core.convert.FromSame r1_wire.Error)
                                      residual)
                                  Pure.pure (r16, commitments2)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r15 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (host_semantic.BuiltSemantics H)
                                    (core.convert.FromSame r1_wire.Error)
                                    residual)
                                Pure.pure (r15, commitments2)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r14 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (host_semantic.BuiltSemantics H)
                                  (core.convert.FromSame r1_wire.Error)
                                  residual)
                              Pure.pure (r14, commitments2)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r13 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (host_semantic.BuiltSemantics H)
                                (core.convert.FromSame r1_wire.Error) residual)
                            Pure.pure (r13, commitments2)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r12 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (host_semantic.BuiltSemantics H)
                              (core.convert.FromSame r1_wire.Error) residual)
                          Pure.pure (r12, commitments2)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r11 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (host_semantic.BuiltSemantics H)
                            (core.convert.FromSame r1_wire.Error) residual)
                        Pure.pure (r11, commitments2)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r10 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (host_semantic.BuiltSemantics H) (core.convert.FromSame
                      r1_wire.Error) residual)
                  Pure.pure (r10, commitments1)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r8 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (host_semantic.BuiltSemantics H) (core.convert.FromSame
                    r1_wire.Error) residual)
                Pure.pure (r8, commitments1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r7 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (host_semantic.BuiltSemantics H) (core.convert.FromSame
                  r1_wire.Error) residual)
              Pure.pure (r7, commitments1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r6 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (host_semantic.BuiltSemantics H) (core.convert.FromSame
                r1_wire.Error) residual)
            Pure.pure (r6, commitments1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (host_semantic.BuiltSemantics H) (core.convert.FromSame
              r1_wire.Error) residual)
          Pure.pure (r5, commitments1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (host_semantic.BuiltSemantics H) (core.convert.FromSame
            r1_wire.Error) residual)
        Pure.pure (r4, commitments1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (host_semantic.BuiltSemantics H) (core.convert.FromSame
          r1_wire.Error) residual)
      Pure.pure (r2, commitments1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (host_semantic.BuiltSemantics H) (core.convert.FromSame r1_wire.Error)
        residual)
    Pure.pure (r1, commitments)

theorem complete_result
  {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H)
  (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
  (CommitmentsInst : host_semantic.Commitments T2)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1)
  (commitments : T2) (hash : H) (variant : transport.Variant) :
  erase (produce (H := H) (T1 := T1) (T2 := T2) aspis_coredigestDigest32Inst coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst CommitmentsInst public1 c1 d g h1_padding helper commitments hash variant) = host_semantic.build_with_helper_mode (H := H) (T1 := T1) (T2 := T2) aspis_coredigestDigest32Inst coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst CommitmentsInst public1 c1 d g h1_padding helper commitments hash variant := by
  unfold produce
  conv_rhs => unfold host_semantic.build_with_helper_mode
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_043.complete_result,PV_L1D_Source_044.complete_result,PV_L1D_Source_045.complete_result,PV_L1D_Source_047.complete_result,PV_L1D_Source_049.complete_result,PV_L1D_Source_051.complete_result,PV_L1D_Source_052.complete_result,PV_L1D_Source_055.complete_result,PV_L1D_Source_056.complete_result,PV_L1D_Source_066.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_043.complete_result,PV_L1D_Source_044.complete_result,PV_L1D_Source_045.complete_result,PV_L1D_Source_047.complete_result,PV_L1D_Source_049.complete_result,PV_L1D_Source_051.complete_result,PV_L1D_Source_052.complete_result,PV_L1D_Source_055.complete_result,PV_L1D_Source_056.complete_result,PV_L1D_Source_066.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_043.complete_result,PV_L1D_Source_044.complete_result,PV_L1D_Source_045.complete_result,PV_L1D_Source_047.complete_result,PV_L1D_Source_049.complete_result,PV_L1D_Source_051.complete_result,PV_L1D_Source_052.complete_result,PV_L1D_Source_055.complete_result,PV_L1D_Source_056.complete_result,PV_L1D_Source_066.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_067
