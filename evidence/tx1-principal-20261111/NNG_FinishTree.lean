import NNG_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishTree
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted
open NMT_CallTree (Code invoke erase)
/-- SAME typed call arguments and complete replies on the fresh emitted body.
The Parent retains original inputs. Repeated pure getter values are reused
exactly as in the actual emission; no callee-law assumption is added. -/
def tree {H W : Type} (c : Calls) (s : Parent H W) : Code (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer

  let r ←
    invoke "rounds" (prefix1,transcript) (c.c10 aspis_coredigestDigest32Inst prefix1 transcript)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    invoke "mark2" (obs,2#u8) (c.c9 obs 2#u8)
    let r1 ← invoke "claims" (prefix1) (c.c8 prefix1)
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        invoke "terminal" (public1,val1,alpha,challenges) (c.c7 public1 val1 alpha challenges)
      let r3 ←
        c.c1
          (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
          aspis_coredigestDigest32Inst) r2 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        invoke "mark3" (obs,3#u8) (c.c9 obs 3#u8)
        let a ←
          c.c0 16#usize
            (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
            aspis_coredigestDigest32Inst) val1
        let a1 ←
          c.c0 10#usize
            (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
            aspis_coredigestDigest32Inst) val1
        let a2 ← Array.index_usize val1 0#usize
        let q ← Array.index_usize a2 27#usize
        let mask ←
          invoke "mask" (a,a1,q,alpha) (c.c6 a a1 q alpha)
        let r4 ← invoke "record25" (prefix1,25#u8) (c.c11 prefix1 25#u8)
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue vr =>
          let r5 ← invoke "extra" (vr,87#usize) (c.c15 29#usize vr 87#usize)
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let q1 ← invoke "multiply" (challenges.eta,val2) (c.c5 challenges.eta val2)
            let q2 ← invoke "addMask" (mask,q1) (c.c4 mask q1)
            let q3 ← Array.index_usize val3 28#usize
            let masked_terminal ← invoke "addExtra" (q2,q3) (c.c4 q2 q3)
            let b ←
              core.cmp.PartialEq.ne.trait_default
                (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c.c3) running
                masked_terminal
            if b
            then pure (core.result.Result.Err r1_wire.Error.Terminal)
            else
              invoke "mark4" (obs,4#u8) (c.c9 obs 4#u8)
              let state_before_z0 ←
                invoke "state" (transcript1) (c.c14 aspis_coredigestDigest32Inst transcript1)
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue vr1 =>
                let (r6, transcript2) ←
                  invoke "circle0" (transcript1,vr1) (c.c13 aspis_coredigestDigest32Inst transcript1 vr1)
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let r7 ← invoke "record26" (prefix1,26#u8) (c.c11 prefix1 26#u8)
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue vr2 =>
                    let r8 ←
                      invoke "beforeZ1" (vr2,0#usize) (c.c15 29#usize vr2 0#usize)
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue vr3 =>
                        let (r9, transcript3) ←
                          invoke "circle1" (transcript2,vr3) (c.c13 aspis_coredigestDigest32Inst transcript2 vr3)
                        let cf10 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf10 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          invoke "mark5" (obs,5#u8) (c.c9 obs 5#u8)
                          let b1 ←
                            c.c2
                              val4 val6
                          if b1
                          then
                            pure (core.result.Result.Err
                              r1_wire.Error.EqualCirclePoints)
                          else
                            let r10 ← invoke "payload2" (prefix1,2#u8) (c.c12 prefix1 2#u8)
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r10
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val7
                              =>
                              let r11 ←
                                core.array.TryFromArrayCopySlice.try_from
                                  32#usize core.marker.CopyU8 val7
                              let a3 ←
                                core.result.Result.unwrap
                                  core.fmt.DebugTryFromSliceError r11
                              pure (core.result.Result.Ok
                                {
                                  roots :=
                                    (Array.make 2#usize [
                                      prefix1.c1_root, a3
                                      ]),
                                  challenges,
                                  alpha,
                                  claims := val1,
                                  extra := val3,
                                  before_z1 := val5,
                                  state_before_z0,
                                  z := (Array.make 2#usize [ val4, val6 ]),
                                  transcript := transcript3
                                })
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (r1_semantic.Verified H) (core.convert.FromSame
                                r1_wire.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (r1_semantic.Verified H) (core.convert.FromSame
                            r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (r1_semantic.Verified H) (core.convert.FromSame
                          r1_wire.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (r1_semantic.Verified H) (core.convert.FromSame
                        r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (r1_semantic.Verified H) (core.convert.FromSame
                      r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (r1_semantic.Verified H) (core.convert.FromSame
                    r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (r1_semantic.Verified H) (core.convert.FromSame
                  r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

end AspisR1.NNG_FinishTree
