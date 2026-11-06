import NJG_FinishTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_FinishBody
open Aeneas Aeneas.Std Result ControlFlow Error
structure Boundaries (H : Type) where
 fromFn : {T F : Type} → (N : Usize) → core.ops.function.FnMut F Usize T → F → Result (Array T N)
 mapError : {T E F O : Type} → core.ops.function.FnOnce O E F → core.result.Result T E → O → Result (core.result.Result T F)
 qEq : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool
 pointEq : aspis_core.circle.SecureCirclePoint → aspis_core.circle.SecureCirclePoint → Result Bool
 add : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
 mul : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
 mask : Array aspis_core.field.QM31 16#usize → Array aspis_core.field.QM31 10#usize → aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31
 terminal : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Array (Array aspis_core.field.QM31 29#usize) 3#usize → Array aspis_core.field.QM31 10#usize → aspis_core.state_only_prefix.r0.Challenges → Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
 claims : r1_wire.Prefix → Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error)
 rounds : aspis_core.digest.Digest32 H → r1_wire.Prefix → r1_wire.SemanticTranscript H → Result (core.result.Result (aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript H) r1_wire.Error)
 record : r1_wire.Prefix → U8 → Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 payload : r1_wire.Prefix → U8 → Result (core.result.Result (Slice U8) r1_wire.Error)
 circle : aspis_core.digest.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Result (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H)
 state : aspis_core.digest.Digest32 H → r1_wire.SemanticTranscript H → Result (Array U8 32#usize)
 decode : (N : Usize) → r1_wire.ValidatedRecord → Usize → Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)

def qCmp {H : Type} (B : Boundaries H) : core.cmp.PartialEq aspis_core.field.QM31 aspis_core.field.QM31 where
 eq := B.qEq
 ne := fun a b=>do let equal←B.qEq a b;ok (!equal)
/-- [aspis_r1_cost_probe::r1_semantic::mark]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 75:0-80:1 -/
def r1_semantic.mark
  (obs : Option (verifier.Phase → Result Unit)) (i : Std.U8) :
  Result Unit
  := do
  ok ()

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#2<'_0, H>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 253:30-253:51 -/
def
  r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.verify_finish.closure_2 H) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 × (r1_semantic.verify_finish.closure_2 H))
  := do
  let i ← lift (Std.Usize.wrapping_add 16#usize tupled_args)
  let a ← Array.index_usize c 0#usize
  let q ← Array.index_usize a i
  ok (q, c)

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#2<'_0, H>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 253:30-253:51 -/
def
  r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.verify_finish.closure_2 H) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      aspis_coredigestDigest32Inst c i
  ok q

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#2<'_0, H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 253:30-253:51 -/
@[reducible]
def
  r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (r1_semantic.verify_finish.closure_2 H) Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    aspis_coredigestDigest32Inst
}

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#2<'_0, H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 253:30-253:51 -/
@[reducible]
def
  r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnMut (r1_semantic.verify_finish.closure_2 H) Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    aspis_coredigestDigest32Inst
  call_mut :=
    r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    aspis_coredigestDigest32Inst
}

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#1<'_0, H>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 252:30-252:46 -/
def
  r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.verify_finish.closure_1 H) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 × (r1_semantic.verify_finish.closure_1 H))
  := do
  let a ← Array.index_usize c 0#usize
  let q ← Array.index_usize a tupled_args
  ok (q, c)

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#1<'_0, H>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 252:30-252:46 -/
def
  r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.verify_finish.closure_1 H) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      aspis_coredigestDigest32Inst c i
  ok q

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#1<'_0, H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 252:30-252:46 -/
@[reducible]
def
  r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (r1_semantic.verify_finish.closure_1 H) Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
    aspis_coredigestDigest32Inst
}

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure#1<'_0, H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 252:30-252:46 -/
@[reducible]
def
  r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnMut (r1_semantic.verify_finish.closure_1 H) Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    aspis_coredigestDigest32Inst
  call_mut :=
    r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    aspis_coredigestDigest32Inst
}

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure<H>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 249:17-249:34 -/
def
  r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (c : r1_semantic.verify_finish.closure H)
  (tupled_args : aspis_core.state_only_prefix.r0.Error) :
  Result r1_wire.Error
  := do
  ok AspisR1PublicPreparation.r1_wire.Error.Public

/-- Trait implementation: [aspis_r1_cost_probe::r1_semantic::verify_finish::{impl core::ops::function::FnOnce<(aspis_core::state_only_prefix::r0::Error,), aspis_r1_cost_probe::r1_wire::Error> for aspis_r1_cost_probe::r1_semantic::verify_finish::closure<H>}]
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 249:17-249:34 -/
@[reducible]
def
  r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
  core.ops.function.FnOnce (r1_semantic.verify_finish.closure H)
  aspis_core.state_only_prefix.r0.Error r1_wire.Error := {
  call_once :=
    r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coredigestDigest32Inst
}

/-- [aspis_r1_cost_probe::r1_semantic::verify_finish]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 232:0-308:1 -/
def r1_semantic.verify_finish
  {H : Type} (B : Boundaries H) (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
  (challenges : aspis_core.state_only_prefix.r0.Challenges)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ←
    B.rounds aspis_coredigestDigest32Inst prefix1 transcript
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    r1_semantic.mark obs 2#u8
    let r1 ← B.claims prefix1
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        B.terminal
          public1 val1 alpha challenges
      let r3 ←
        B.mapError
          (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
          aspis_coredigestDigest32Inst) r2 ()
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        r1_semantic.mark obs 3#u8
        let a ←
          B.fromFn 16#usize
            (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
            aspis_coredigestDigest32Inst) val1
        let a1 ←
          B.fromFn 10#usize
            (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
            aspis_coredigestDigest32Inst) val1
        let a2 ← Array.index_usize val1 0#usize
        let q ← Array.index_usize a2 27#usize
        let mask ←
          B.mask a a1 q
            alpha
        let r4 ← B.record prefix1 25#u8
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue vr =>
          let r5 ← B.decode 29#usize vr 87#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let q1 ← B.mul challenges.eta val2
            let q2 ← B.add mask q1
            let q3 ← Array.index_usize val3 28#usize
            let masked_terminal ← B.add q2 q3
            let b ←
              core.cmp.PartialEq.ne.trait_default
                (qCmp B) running
                masked_terminal
            if b
            then ok (core.result.Result.Err AspisR1PublicPreparation.r1_wire.Error.Terminal)
            else
              r1_semantic.mark obs 4#u8
              let state_before_z0 ←
                B.state
                  aspis_coredigestDigest32Inst transcript1
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue vr1 =>
                let (r6, transcript2) ←
                  B.circle
                    aspis_coredigestDigest32Inst transcript1 vr1
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let r7 ← B.record prefix1 26#u8
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue vr2 =>
                    let r8 ←
                      B.decode 29#usize vr2 0#usize
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue vr3 =>
                        let (r9, transcript3) ←
                          B.circle
                            aspis_coredigestDigest32Inst transcript2 vr3
                        let cf10 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf10 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          r1_semantic.mark obs 5#u8
                          let b1 ←
                            B.pointEq
                              val4 val6
                          if b1
                          then
                            ok (core.result.Result.Err
                              AspisR1PublicPreparation.r1_wire.Error.EqualCirclePoints)
                          else
                            let r10 ← B.payload prefix1 2#u8
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


theorem mark_value (obs : Option (verifier.Phase → Result Unit)) (i : U8) : r1_semantic.mark obs i=ok () := rfl
#print axioms mark_value
#print axioms r1_semantic.verify_finish
end AspisR1.NJG_FinishBody
end
