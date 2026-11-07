import NNG_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceSuffixes
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted

def f_a3 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
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

def f_r11 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (val7 : Slice U8) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r11 ←
    core.array.TryFromArrayCopySlice.try_from
      32#usize core.marker.CopyU8 val7
  f_a3 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 r11

def f_r10 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r10 ← c.c12 prefix1 2#u8
  let cf11 ←
    core.result.Result.Insts.CoreOpsTry.branch r10
  match cf11 with
  | core.ops.control_flow.ControlFlow.Continue val7
    =>
    f_r11 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7
  | core.ops.control_flow.ControlFlow.Break residual
    =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_circleGuard {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (b1 : Bool) : Result (Output H) := do
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
    f_r10 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6

def f_b1 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let b1 ←
    c.c2
      val4 val6
  f_circleGuard c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 b1

def f_mark5 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  c.c9 obs 5#u8
  f_b1 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6

def f_r9 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (vr3 : r1_wire.ValidatedRecord) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let (r9, transcript3) ←
    c.c13
      aspis_coredigestDigest32Inst transcript2 vr3
  let cf10 ←
    core.result.Result.Insts.CoreOpsTry.branch r9
  match cf10 with
  | core.ops.control_flow.ControlFlow.Continue val6 =>
    f_mark5 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r8 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (vr2 : r1_wire.ValidatedRecord) (r7 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r8 ←
    c.c15 29#usize vr2 0#usize
  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
  match cf8 with
  | core.ops.control_flow.ControlFlow.Continue val5 =>
    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r7
    match cf9 with
    | core.ops.control_flow.ControlFlow.Continue vr3 =>
      f_r9 c s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame
        r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r7 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r7 ← c.c11 prefix1 26#u8
  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
  match cf7 with
  | core.ops.control_flow.ControlFlow.Continue vr2 =>
    f_r8 c s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_r6 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (vr1 : r1_wire.ValidatedRecord) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let (r6, transcript2) ←
    c.c13
      aspis_coredigestDigest32Inst transcript1 vr1
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue val4 =>
    f_r7 c s alpha val1 val3 state_before_z0 transcript2 val4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_state_before_z0 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let state_before_z0 ←
    c.c14
      aspis_coredigestDigest32Inst transcript1
  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf5 with
  | core.ops.control_flow.ControlFlow.Continue vr1 =>
    f_r6 c s alpha transcript1 val1 val3 state_before_z0 vr1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame
      r1_wire.Error) residual

def f_mark4 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  c.c9 obs 4#u8
  f_state_before_z0 c s alpha transcript1 val1 val3 r4

def f_terminalGuard {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (b : Bool) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  if b
  then ok (core.result.Result.Err r1_wire.Error.Terminal)
  else
    f_mark4 c s alpha transcript1 val1 val3 r4

def f_b {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (masked_terminal : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let b ←
    core.cmp.PartialEq.ne.trait_default
      (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c.c3) running
      masked_terminal
  f_terminalGuard c s alpha transcript1 val1 val3 b r4

def f_masked_terminal {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (q2 : Q) (q3 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let masked_terminal ← c.c4 q2 q3
  f_b c s running masked_terminal alpha transcript1 val1 val3 r4

def f_q3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (q2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q3 ← Array.index_usize val3 28#usize
  f_masked_terminal c s running q2 q3 alpha transcript1 val1 val3 r4

def f_q2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (mask : Q) (q1 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q2 ← c.c4 mask q1
  f_q3 c s running q2 alpha transcript1 val1 val3 r4

def f_q1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q1 ← c.c5 challenges.eta val2
  f_q2 c s running mask q1 alpha transcript1 val1 val3 r4

def f_r5 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (vr : r1_wire.ValidatedRecord) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r5 ← c.c15 29#usize vr 87#usize
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    f_q1 c s running val2 mask alpha transcript1 val1 val3 r4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_r4 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r4 ← c.c11 prefix1 25#u8
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue vr =>
    f_r5 c s running val2 mask alpha transcript1 val1 vr r4
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_mask {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (q : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let mask ←
    c.c6 a a1 q
      alpha
  f_r4 c s running val2 mask alpha transcript1 val1

def f_q {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) (a2 : K29) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let q ← Array.index_usize a2 27#usize
  f_mask c s running val2 q alpha transcript1 val1 a a1

def f_a2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a2 ← Array.index_usize val1 0#usize
  f_q c s running val2 alpha transcript1 val1 a a1 a2

def f_a1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a1 ←
    c.c0 10#usize
      (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      aspis_coredigestDigest32Inst) val1
  f_a2 c s running val2 alpha transcript1 val1 a a1

def f_a {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let a ←
    c.c0 16#usize
      (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      aspis_coredigestDigest32Inst) val1
  f_a1 c s running val2 alpha transcript1 val1 a

def f_mark3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  c.c9 obs 3#u8
  f_a c s running val2 alpha transcript1 val1

def f_r3 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (r2 : core.result.Result Q aspis_core.state_only_prefix.r0.Error) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r3 ←
    c.c1
      (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coredigestDigest32Inst) r2 ()
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val2 =>
    f_mark3 c s running val2 alpha transcript1 val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
      residual

def f_r2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r2 ←
    c.c7
      public1 val1 alpha challenges
  f_r3 c s running alpha transcript1 val1 r2

def f_r1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r1 ← c.c8 prefix1
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    f_r2 c s running alpha transcript1 val1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

def f_mark2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  c.c9 obs 2#u8
  f_r1 c s running alpha transcript1

def f_r {H W : Type} (c : Calls) (s : Parent H W) : Result (Output H) := do
  let aspis_coredigestDigest32Inst := s.digest
  let public1 := s.publicValue
  let prefix1 := s.prefixValue
  let transcript := s.transcript
  let challenges := s.challenges
  let obs := s.observer
  let r ←
    c.c10 aspis_coredigestDigest32Inst prefix1 transcript
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (running, alpha, transcript1) := val
    f_mark2 c s running alpha transcript1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

end AspisR1.NNG_SourceSuffixes
