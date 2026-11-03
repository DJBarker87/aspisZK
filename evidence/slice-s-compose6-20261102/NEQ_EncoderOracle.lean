import NED_EncoderCallDomains
import NEM_ValidatorComposed
set_option autoImplicit false
noncomputable section
namespace NEQ_EncoderOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
open NED_EncoderTrace (Call R)
abbrev Validate := Statement → Result (core.result.Result Unit NBN_StatementResult.Error)
abbrev Pay := Statement → Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Late := NEE_ValidatorMutation.Late
abbrev Digest := Array U32 8#usize → Result (Array U8 32#usize)
def payStep (pay : Pay) (s : Statement) (anchor : Array U8 32#usize) (late : Slice U8) : R × List Call :=
  let r : R := do
    let pay ← pay s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok a => ok (.Ok ((NBN_StatementEncoderSummary.prefixBytes s anchor ++ late.val) ++ a.val))
  (r,[.payment s])

def lateStep (pay : Pay) (late : Late) (s : Statement) (anchor : Array U8 32#usize) : R × List Call :=
  let arg := (common s).lane_transition
  let out := NBN_LateResult.zero
  match late arg out with
  | .fail e => (.fail e,[.late arg out])
  | .div => (.div,[.late arg out])
  | .ok (.Err e,_) => (ok (.Err (.LaneTransition e)),[.late arg out])
  | .ok (.Ok _,late) => ((payStep pay s anchor late).1,.late arg out :: (payStep pay s anchor late).2)

def anchorStep (pay : Pay) (late : Late) (digest : Digest) (s : Statement) : R × List Call :=
  let d := (common s).historical_global_anchor
  match digest d with
  | .fail e => (.fail e,[.digest d])
  | .div => (.div,[.digest d])
  | .ok anchor => ((lateStep pay late s anchor).1,.digest d :: (lateStep pay late s anchor).2)

def run (validate : Validate) (pay : Pay) (late : Late) (digest : Digest) (s : Statement) : R × List Call :=
  let validation := validate s
  match validation with
  | .fail e => (.fail e,[.validate s])
  | .div => (.div,[.validate s])
  | .ok (.Err e) => (ok (.Err e),[.validate s])
  | .ok (.Ok _) => ((anchorStep pay late digest s).1,.validate s :: (anchorStep pay late digest s).2)

theorem pay_substitution (s : Statement) (anchor : Array U8 32#usize) (out : Slice U8) :
    payStep NEM_PaymentReached.pay s anchor out = NED_EncoderTrace.payStep s anchor out := by
  unfold payStep NED_EncoderTrace.payStep
  rw [NEM_PaymentReached.payment_instance]
  rfl

theorem late_substitution (s : Statement) (anchor : Array U8 32#usize) :
    lateStep NEM_PaymentReached.pay NEM_LateOracle.late s anchor = NED_EncoderTrace.lateStep s anchor := by
  unfold lateStep NED_EncoderTrace.lateStep
  dsimp only
  have same : NEM_LateOracle.late (common s).lane_transition NBN_LateResult.zero =
      NBN_LateSummary.run NED_EncoderTrace.enc (common s).lane_transition NBN_LateResult.zero :=
    (NED_SubtreeComposition.late_encode _ _).symm
  rw [same]
  cases h : NBN_LateSummary.run NED_EncoderTrace.enc (common s).lane_transition NBN_LateResult.zero with
  | fail e => rfl
  | div => rfl
  | ok pair => cases pair with
    | mk status out => cases status with
      | Err e => rfl
      | Ok u =>
        simp only []
        rw [pay_substitution]

theorem anchor_substitution (s : Statement) :
    anchorStep NEM_PaymentReached.pay NEM_LateOracle.late atomic_statement.encode_digest_canonical s =
      NED_EncoderTrace.anchorStep s := by
  unfold anchorStep NED_EncoderTrace.anchorStep NED_EncoderTrace.enc
  dsimp only
  cases h : atomic_statement.encode_digest_canonical (common s).historical_global_anchor with
  | fail e => rfl
  | div => rfl
  | ok anchor =>
    simp only []
    rw [late_substitution]

theorem substitution (s : Statement) :
    run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NEM_PaymentReached.pay NEM_LateOracle.late atomic_statement.encode_digest_canonical s =
      NED_EncoderTrace.run s := by
  unfold run NED_EncoderTrace.run
  rw [← NED_CodecComposition.validator s]
  change (match NED_ExecutionComposition.validatorReference s with
    | .fail e => _ | .div => _ | .ok (.Err e) => _ | .ok (.Ok u) => _) = _
  cases h : NED_ExecutionComposition.validatorReference s with
  | fail e => rfl
  | div => rfl
  | ok status => cases status with
    | Err e => rfl
    | Ok u =>
      simp only []
      rw [anchor_substitution]

theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NEM_PaymentReached.pay NEM_LateOracle.late atomic_statement.encode_digest_canonical s
    (observed.1,state,observed.2) =
      (NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),
       state,(NED_EncoderTrace.run s).2) := by
  dsimp only
  rw [substitution,NED_EncoderTrace.erases]

#print axioms pay_substitution
#print axioms late_substitution
#print axioms anchor_substitution
#print axioms substitution
#print axioms result_state_effects
end NEQ_EncoderOracle
