import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix055
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.build_with_helper_mode`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error)) (CommitmentsInst : host_semantic.Commitments T2) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1) (commitments : T2) (hash : H) (variant : transport.Variant) (out : Payload (host_semantic.check_semantic_columns c1 d g)) : Result ((core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error)
    × T2) := do
  let r := out
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (r1, commitments1) ← CommitmentsInst.c1 commitments c1 d
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r2 ←
        aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
          public1
      let r3 ←
        core.result.Result.map_err
          (host_semantic.build_with_helper_mode.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
          aspis_coredigestDigest32Inst
          coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
          CommitmentsInst) r2 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s := alloc.vec.Vec.deref val1
        let r4 ←
          host_wire.SemanticTranscript.new aspis_coredigestDigest32Inst hash s
            val
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s1 ← Aeneas.Std.lift (Array.to_slice val)
          let bytes ← alloc.slice.Slice.to_vec core.clone.CloneU8 s1
          let s2 ← Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
          let (r5, val3, bytes1) ←
            host_semantic.semantic_row aspis_coredigestDigest32Inst 0#u8 s2
              val2 bytes
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let s3 ← Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
            let (r6, val5, bytes2) ←
              host_semantic.semantic_row aspis_coredigestDigest32Inst 1#u8 s3
                val3 bytes1
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val6 =>
              let r7 ←
                coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst.call_once
                  helper (val4, val6)
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val7 =>
                let (s4, deref_mut_back) ←
                  Aeneas.Std.lift (alloc.vec.Vec.deref_mut val7)
                let s5 ← Aeneas.Std.lift (Array.to_slice h1_padding)
                let (r8, s6) ←
                  aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
                    s4 s5
                let r9 ←
                  core.result.Result.map_err
                    (host_semantic.build_with_helper_mode.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
                    aspis_coredigestDigest32Inst
                    coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst
                    CommitmentsInst) r8 ()
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r9
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let val8 := deref_mut_back s6
                  let i := alloc.vec.Vec.len val8
                  if i != 1024#usize
                  then
                    ok (core.result.Result.Err r1_wire.Error.Public,
                      commitments1)
                  else
                    let s7 := alloc.vec.Vec.deref val8
                    let o ←
                      aspis_statement.state_only_semantic.state_only_copy_helper_sum
                        s7
                    let q ← aspis_core.field.QM31.ZERO
                    let b ←
                      core.cmp.PartialEq.ne.trait_default
                        (core.option.Option.Insts.CoreCmpPartialEqOption
                        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31) o
                        (some q)
                    if b
                    then
                      ok (core.result.Result.Err r1_wire.Error.Public,
                        commitments1)
                    else
                      let s8 := alloc.vec.Vec.deref val8
                      let (r10, commitments2) ←
                        CommitmentsInst.c2 commitments1 s8 g
                      let cf8 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let s9 ← Aeneas.Std.lift (Array.to_slice val9)
                        let (r11, val10, bytes3) ←
                          host_semantic.semantic_row
                            aspis_coredigestDigest32Inst 2#u8 s9 val5 bytes2
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val11 =>
                          let (r12, val12, bytes4) ←
                            host_semantic.zc_rows aspis_coredigestDigest32Inst
                              val10 bytes3
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val13 =>
                            let s10 ←
                              Aeneas.Std.lift (Array.to_slice (Std.Array.empty Std.U8))
                            let (r13, val14, bytes5) ←
                              host_semantic.semantic_row
                                aspis_coredigestDigest32Inst 13#u8 s10 val12
                                bytes4
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val15
                              =>
                              let columns ←
                                host_semantic.lift_columns c1 val8 g d
                              let dc ←
                                transport.Variant.coefficients
                                  aspis_core.field.QM31.Insts.CoreMarkerCopy
                                  variant d
                              let mask_sum ←
                                host_semantic.initial_mask_sum columns
                              let mask_sum1 ←
                                host_semantic.add_d_tail mask_sum dc
                              let we ←
                                aspis_core.field.wide_exact.WideExact.from_qm31
                                  mask_sum1
                              let a ←
                                aspis_core.field.wide_exact.WideExact.to_le_bytes
                                  we
                              let s11 ← Aeneas.Std.lift (Array.to_slice a)
                              let (r14, val16, bytes6) ←
                                host_semantic.semantic_row
                                  aspis_coredigestDigest32Inst 14#u8 s11 val14
                                  bytes5
                              let cf12 ←
                                core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf12 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val17 =>
                                let (r15, val18, bytes7) ←
                                  host_sumcheck.prove_sumcheck
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
                                let cf13 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf13 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val19 =>
                                  let (alpha, _) := val19
                                  let r16 ←
                                    host_semantic.point_claims columns alpha
                                  let cf14 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf14 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val20 =>
                                    let state_before_z0 ←
                                      host_wire.SemanticTranscript.impl.state
                                        aspis_coredigestDigest32Inst val18
                                    let q1 ← Array.index_usize alpha 8#usize
                                    let q2 ← Array.index_usize alpha 9#usize
                                    let extras ←
                                      host_semantic.extra_claims columns
                                        variant q1 q2
                                    let v ←
                                      host_semantic.claim_bytes val20 extras
                                    let s12 := alloc.vec.Vec.deref v
                                    let r17 ← host_wire.record 25#u8 s12
                                    let cf15 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf15 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val21 =>
                                      let s13 := alloc.vec.Vec.deref val21
                                      let (r18, val22) ←
                                        host_wire.SemanticTranscript.challenge_reference_circle_point
                                          aspis_coredigestDigest32Inst val18
                                          25#u8 s13
                                      let cf16 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf16 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val23 =>
                                        let s14 := alloc.vec.Vec.deref val21
                                        let bytes8 ←
                                          alloc.vec.Vec.extend_from_slice
                                            core.clone.CloneU8 bytes7 s14
                                        let v1 ←
                                          host_semantic.endpoint_bytes columns
                                            variant val23
                                        let s15 := alloc.vec.Vec.deref v1
                                        let r19 ← host_wire.record 26#u8 s15
                                        let cf17 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf17 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val24 =>
                                          let s16 := alloc.vec.Vec.deref val24
                                          let (r20, val25) ←
                                            host_wire.SemanticTranscript.challenge_reference_circle_point
                                              aspis_coredigestDigest32Inst
                                              val22 26#u8 s16
                                          let cf18 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf18 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val26 =>
                                            let s17 :=
                                              alloc.vec.Vec.deref val24
                                            let bytes9 ←
                                              alloc.vec.Vec.extend_from_slice
                                                core.clone.CloneU8 bytes8 s17
                                            let b1 ←
                                              aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
                                                val23 val26
                                            if b1
                                            then
                                              ok (core.result.Result.Err
                                                r1_wire.Error.EqualCirclePoints,
                                                commitments2)
                                            else
                                              ok (core.result.Result.Ok
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
                                            let r21 ←
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                (host_semantic.BuiltSemantics
                                                H) (core.convert.FromSame
                                                r1_wire.Error) residual
                                            ok (r21, commitments2)
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          let r20 ←
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (host_semantic.BuiltSemantics H)
                                              (core.convert.FromSame
                                              r1_wire.Error) residual
                                          ok (r20, commitments2)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        let r19 ←
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            (host_semantic.BuiltSemantics H)
                                            (core.convert.FromSame
                                            r1_wire.Error) residual
                                        ok (r19, commitments2)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      let r18 ←
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (host_semantic.BuiltSemantics H)
                                          (core.convert.FromSame r1_wire.Error)
                                          residual
                                      ok (r18, commitments2)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    let r17 ←
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (host_semantic.BuiltSemantics H)
                                        (core.convert.FromSame r1_wire.Error)
                                        residual
                                    ok (r17, commitments2)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  let r16 ←
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      (host_semantic.BuiltSemantics H)
                                      (core.convert.FromSame r1_wire.Error)
                                      residual
                                  ok (r16, commitments2)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                let r15 ←
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    (host_semantic.BuiltSemantics H)
                                    (core.convert.FromSame r1_wire.Error)
                                    residual
                                ok (r15, commitments2)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              let r14 ←
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (host_semantic.BuiltSemantics H)
                                  (core.convert.FromSame r1_wire.Error)
                                  residual
                              ok (r14, commitments2)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            let r13 ←
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (host_semantic.BuiltSemantics H)
                                (core.convert.FromSame r1_wire.Error) residual
                            ok (r13, commitments2)
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          let r12 ←
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (host_semantic.BuiltSemantics H)
                              (core.convert.FromSame r1_wire.Error) residual
                          ok (r12, commitments2)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        let r11 ←
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (host_semantic.BuiltSemantics H)
                            (core.convert.FromSame r1_wire.Error) residual
                        ok (r11, commitments2)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r10 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (host_semantic.BuiltSemantics H) (core.convert.FromSame
                      r1_wire.Error) residual
                  ok (r10, commitments1)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r8 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (host_semantic.BuiltSemantics H) (core.convert.FromSame
                    r1_wire.Error) residual
                ok (r8, commitments1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r7 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (host_semantic.BuiltSemantics H) (core.convert.FromSame
                  r1_wire.Error) residual
              ok (r7, commitments1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r6 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (host_semantic.BuiltSemantics H) (core.convert.FromSame
                r1_wire.Error) residual
            ok (r6, commitments1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (host_semantic.BuiltSemantics H) (core.convert.FromSame
              r1_wire.Error) residual
          ok (r5, commitments1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (host_semantic.BuiltSemantics H) (core.convert.FromSame
            r1_wire.Error) residual
        ok (r4, commitments1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (host_semantic.BuiltSemantics H) (core.convert.FromSame
          r1_wire.Error) residual
      ok (r2, commitments1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (host_semantic.BuiltSemantics H) (core.convert.FromSame r1_wire.Error)
        residual
    ok (r1, commitments)


end R1Z.PV_RE_NoCatchSuffix055
pv_no_catch_binds ProverRwFull.host_semantic.build_with_helper_mode
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix055.continueAfter
