import NKA_FinishTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_FinishStages
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev Out (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
/-- Literal source suffix around OPEN terminal256; complete normalized Rust
Result. This is a source equation, never a free terminal premise at a root. -/
def afterTerminal (reservation : NP6_StdModel.Reservation) {H : Type}
 (aspis_coreDigest32Inst : aspis_core.Digest32 H)
 (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H)
 (val1 : Claims) (r3 : core.result.Result Q r1_wire.Error) : Result (Out H) := do
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    VerifyPrefix.mark none 3#u8
    let a ←
      (IDa_Deployed.boundaries reservation).fromFn 16#usize
        (FinishModel.closureFn9
        aspis_coreDigest32Inst) val1
    let a1 ←
      (IDa_Deployed.boundaries reservation).fromFn 10#usize
        (FinishModel.closureFn5
        aspis_coreDigest32Inst) val1
    let a2 ← Array.index_usize val1 0#usize
    let q ← Array.index_usize a2 27#usize
    let mask ←
      (IDa_Deployed.boundaries reservation).mask a a1 q
        alpha
    let r4 ← r1_wire.Prefix.validated_record prefix1 25#u8
    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
    match cf3 with
    | core.ops.control_flow.ControlFlow.Continue vr =>
      let r5 ← NJM_RoundJoin.R.decode 29#usize vr 87#usize
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val3 =>
        let q1 ← (IDa_Deployed.boundaries reservation).mul challenges.eta val2
        let q2 ← (IDa_Deployed.boundaries reservation).add mask q1
        let q3 ← Array.index_usize val3 28#usize
        let masked_terminal ← (IDa_Deployed.boundaries reservation).add q2 q3
        let b ←
          core.cmp.PartialEq.ne.trait_default
            aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running
            masked_terminal
        if b
        then ok (core.result.Result.Err r1_wire.Error.Terminal)
        else
          VerifyPrefix.mark none 4#u8
          let state_before_z0 ←
            r1_wire.SemanticTranscript.impl.state aspis_coreDigest32Inst
              transcript1
          let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf5 with
          | core.ops.control_flow.ControlFlow.Continue vr1 =>
            let (r6, transcript2) ←
              FinishModel.circle_validated (IDa_Deployed.boundaries reservation)
                aspis_coreDigest32Inst transcript1 vr1
            let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
            match cf6 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let r7 ← r1_wire.Prefix.validated_record prefix1 26#u8
              let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
              match cf7 with
              | core.ops.control_flow.ControlFlow.Continue vr2 =>
                let r8 ←
                  NJM_RoundJoin.R.decode 29#usize vr2 0#usize
                let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                match cf8 with
                | core.ops.control_flow.ControlFlow.Continue val5 =>
                  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf9 with
                  | core.ops.control_flow.ControlFlow.Continue vr3 =>
                    let (r9, transcript3) ←
                      FinishModel.circle_validated (IDa_Deployed.boundaries reservation)
                        aspis_coreDigest32Inst transcript2 vr3
                    let cf10 ←
                      core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf10 with
                    | core.ops.control_flow.ControlFlow.Continue val6 =>
                      VerifyPrefix.mark none 5#u8
                      let b1 ←
                        FinishModel.pointEq
                          val4 val6
                      if b1
                      then
                        ok (core.result.Result.Err
                          r1_wire.Error.EqualCirclePoints)
                      else
                        let r10 ← FinishModel.payload prefix1 2#u8
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch r10
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val7
                          =>
                          let r11 ←
                            core.array.TryFromArrayCopySlice.try_from
                              32#usize core.marker.CopyU8 val7
                          let a3 ←
                            (IDa_Deployed.boundaries reservation).unwrapRoot r11
                          ok (core.result.Result.Ok
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
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (r1_semantic.Verified H) (core.convert.FromSame
                            r1_wire.Error) residual


def afterClaims (reservation : NP6_StdModel.Reservation) {H : Type}
 (aspis_coreDigest32Inst : aspis_core.Digest32 H)
 (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H)
 (r1 : core.result.Result Claims r1_wire.Error) : Result (Out H) := do
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    let r2 ←
      (IDa_Deployed.boundaries reservation).terminal public1
        val1 alpha challenges
    let r3 ←
      core.result.Result.map_err
        (FinishModel.closureFn11
        aspis_coreDigest32Inst) r2 ()
    afterTerminal reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 val1 r3


def afterRounds (reservation : NP6_StdModel.Reservation) {H : Type}
 (aspis_coreDigest32Inst : aspis_core.Digest32 H)
 (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (r : NKA_FinishStages.RoundOut H) : Result (Out H) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    VerifyPrefix.mark none 2#u8
    let r1 ← (IDa_Deployed.boundaries reservation).claims prefix1
    afterClaims reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 r1
  | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (r1_semantic.Verified H) (core.convert.FromSame
                            r1_wire.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (r1_semantic.Verified H) (core.convert.FromSame
                          r1_wire.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (r1_semantic.Verified H) (core.convert.FromSame
                        r1_wire.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (r1_semantic.Verified H) (core.convert.FromSame
                      r1_wire.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (r1_semantic.Verified H) (core.convert.FromSame
                    r1_wire.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (r1_semantic.Verified H) (core.convert.FromSame
                  r1_wire.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

theorem factor (reservation : NP6_StdModel.Reservation) {H : Type}
 (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (r : NKA_FinishStages.RoundOut H) :
 NKA_FinishStages.afterRounds reservation D pub pre challenges r = afterRounds reservation D pub pre challenges r := by rfl

theorem claims_error (reservation : NP6_StdModel.Reservation) {H : Type}
 (aspis_coreDigest32Inst : aspis_core.Digest32 H)
 (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H)
 (e : r1_wire.Error) :
 afterClaims reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 (.Err e) = ok (.Err e) := by rfl

theorem terminal_error (reservation : NP6_StdModel.Reservation) {H : Type}
 (aspis_coreDigest32Inst : aspis_core.Digest32 H)
 (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (prefix1 : r1_wire.Prefix) (challenges : r1_wire.Challenges)
 (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H)
 (val1 : Claims) (e : r1_wire.Error) :
 afterTerminal reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 val1 (.Err e) = ok (.Err e) := by rfl

#print axioms factor
#print axioms claims_error
#print axioms terminal_error
#print factor
end AspisR1.NKQ_FinishStages
end
