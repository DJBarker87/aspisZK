import IDa_Deployed
import NNG_Model134
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacySuffix136
open Aeneas Aeneas.Std Result AspisR1PublicPreparation


abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev K29 := Array Q 29#usize
abbrev Output (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
structure Parent (H W : Type) where
 digest : aspis_core.Digest32 H
 publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public
 prefixValue : r1_wire.Prefix
 transcript : r1_wire.SemanticTranscript H
 challenges : r1_wire.Challenges
 observer : Option (verifier.Phase → Result Unit)

def f_a3 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a3 ←
    B.unwrapRoot r11
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

def f_r11 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (val7 : Slice U8) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r11 ←
    core.array.TryFromArrayCopySlice.try_from
      32#usize core.marker.CopyU8 val7
  f_a3 B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 r11

def f_r10 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r10 ← FinishModel.payload prefix1 2#u8
  let cf11 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf11 with
  | core.ops.control_flow.ControlFlow.Continue val7
    =>
    f_r11 B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7
  | core.ops.control_flow.ControlFlow.Break residual
    =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_circleGuard {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (b1 : Bool) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  if b1
  then
    ok (core.result.Result.Err
      r1_wire.Error.EqualCirclePoints)
  else
    f_r10 B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6

def f_b1 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let b1 ←
    FinishModel.pointEq
      val4 val6
  f_circleGuard B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 b1

def f_mark5 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  VerifyPrefix.mark obs 5#u8
  f_b1 B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6

def f_r9 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (vr3 : r1_wire.ValidatedRecord) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let (r9, transcript3) ←
    FinishModel.circle_validated B
      aspis_coredigestDigest32Inst transcript2 vr3
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r9
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val6 =>
    f_mark5 B s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r8 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (vr2 : r1_wire.ValidatedRecord) (r7 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r8 ←
    AspisS1ExtractedRoundChildren.children.decode 29#usize vr2 0#usize
  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
  match cf8 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
    match cf9 with
    | core.ops.control_flow.ControlFlow.Continue vr3 =>
      f_r9 B s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r7 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r7 ← r1_wire.Prefix.validated_record prefix1 26#u8
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue vr2 =>
    f_r8 B s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r6 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (vr1 : r1_wire.ValidatedRecord) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let (r6, transcript2) ←
    FinishModel.circle_validated B
      aspis_coredigestDigest32Inst transcript1 vr1
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue val4 =>
    f_r7 B s alpha val1 val3 state_before_z0 transcript2 val4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_state_before_z0 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let state_before_z0 ←
    r1_wire.SemanticTranscript.impl.state
      aspis_coredigestDigest32Inst transcript1
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue vr1 =>
    f_r6 B s alpha transcript1 val1 val3 state_before_z0 vr1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_mark4 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  VerifyPrefix.mark obs 4#u8
  f_state_before_z0 B s alpha transcript1 val1 val3 r4

def f_terminalGuard {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (b : Bool) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  if b
  then ok (core.result.Result.Err r1_wire.Error.Terminal)
  else
    f_mark4 B s alpha transcript1 val1 val3 r4

def f_b {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (masked_terminal : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let b ←
    core.cmp.PartialEq.ne.trait_default
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running
      masked_terminal
  f_terminalGuard B s alpha transcript1 val1 val3 b r4

def f_masked_terminal {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (q2 : Q) (q3 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let masked_terminal ← B.add q2 q3
  f_b B s running masked_terminal alpha transcript1 val1 val3 r4

def f_q3 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (q2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q3 ← Array.index_usize val3 28#usize
  f_masked_terminal B s running q2 q3 alpha transcript1 val1 val3 r4

def f_q2 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (mask : Q) (q1 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q2 ← B.add mask q1
  f_q3 B s running q2 alpha transcript1 val1 val3 r4

def f_q1 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q1 ← B.mul challenges.eta val2
  f_q2 B s running mask q1 alpha transcript1 val1 val3 r4

def f_r5 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (vr : r1_wire.ValidatedRecord) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r5 ← AspisS1ExtractedRoundChildren.children.decode 29#usize vr 87#usize
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    f_q1 B s running val2 mask alpha transcript1 val1 val3 r4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_r4 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r4 ← r1_wire.Prefix.validated_record prefix1 25#u8
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    f_r5 B s running val2 mask alpha transcript1 val1 vr r4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_mask {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (q : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let mask ←
    B.mask a a1 q
      alpha
  f_r4 B s running val2 mask alpha transcript1 val1

def f_q {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) (a2 : K29) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q ← Array.index_usize a2 27#usize
  f_mask B s running val2 q alpha transcript1 val1 a a1

def f_a2 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a2 ← Array.index_usize val1 0#usize
  f_q B s running val2 alpha transcript1 val1 a a1 a2

def f_a1 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a1 ←
    B.fromFn 10#usize
      (FinishModel.closureFn5
      aspis_coredigestDigest32Inst) val1
  f_a2 B s running val2 alpha transcript1 val1 a a1

def f_a {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a ←
    B.fromFn 16#usize
      (FinishModel.closureFn9
      aspis_coredigestDigest32Inst) val1
  f_a1 B s running val2 alpha transcript1 val1 a

def f_mark3 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  VerifyPrefix.mark obs 3#u8
  f_a B s running val2 alpha transcript1 val1

def f_r3 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (r2 : core.result.Result Q aspis_core.state_only_prefix.r0.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r3 ←
    core.result.Result.map_err
      (FinishModel.closureFn11
      aspis_coredigestDigest32Inst) r2 ()
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    f_mark3 B s running val2 alpha transcript1 val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_r2 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r2 ←
    B.terminal
      public1 val1 alpha challenges
  f_r3 B s running alpha transcript1 val1 r2

def f_r1 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r1 ← B.claims prefix1
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    f_r2 B s running alpha transcript1 val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

def f_mark2 {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  VerifyPrefix.mark obs 2#u8
  f_r1 B s running alpha transcript1

def f_r {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r ←
    RoundModel.rounds AspisS1ExtractedRoundChildren.children aspis_coredigestDigest32Inst prefix1 transcript
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    f_mark2 B s running alpha transcript1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual


theorem source {H W : Type} (B : FinishModel.Boundaries) (s : Parent H W) :
 f_r B s = FinishModel.finish AspisS1ExtractedRoundChildren.children B s.digest s.publicValue s.prefixValue s.transcript s.challenges s.observer := by
 rfl
#print axioms source
end AspisR1.NNG_LegacySuffix136
