import Lean
import NFY_Part025
import RPz7_S6OuterEncoderContentsV1
import RPz7_DrvC_Installation
import NFY_Part006
import RPz7_S6NativeAfterstateDecoderFactoredV1

-- BEGIN copied NBN_LateInvariant: lean/NBN_LateInvariant.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_LateInvariant
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open NFY_NBN_StatementResult

theorem value_length (s : NFY_NBN_LateTail.Statement) (output : Slice U8) :
    (NFY_NBN_LateTail.value s output).length = output.length := by
  unfold NFY_NBN_LateTail.value
  cases NFY_NBH_LiveValidator.result s.live_snapshot with
  | Err e => rfl
  | Ok u =>
    cases NFY_NBH_Validators.afterResult s.candidate_afterstate <;>
      simp only [Slice.length,Slice.setSlice!,List.length_setSlice!]

/-- All 1520-byte caller pre-states; exact SAME successful bytes and length. -/
theorem ready (s : NFY_NBN_LateTail.Statement)
    (valid : lateStatus s = .Ok ()) (output : Slice U8) (size : output.length = 1520) :
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s output =
      ok (.Ok (),NFY_NBN_LateTail.value s NFY_NBN_LateResult.header) := by
  rw [NFY_NBN_LateResult.source,if_neg (not_not.mpr size)]
  unfold lateStatus at valid
  split at valid
  · cases valid
  · rename_i index
    rw [if_neg index]
    rw [valid]

theorem statement_ready (s : Statement)
    (valid : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ()))
    (output : Slice U8) (size : output.length = 1520) :
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 (common s).lane_transition output =
      ok (.Ok (),NFY_NBN_LateTail.value (common s).lane_transition NFY_NBN_LateResult.header) ∧
    (NFY_NBN_LateTail.value (common s).lane_transition NFY_NBN_LateResult.header).length = 1520 := by
  exact ⟨ready _ (NFY_NBN_StatementDomains.lane_late s valid).2 output size,
    (value_length _ _).trans NFY_NBN_LateResult.header_length⟩

#print axioms value_length
#print axioms ready
#print axioms statement_ready
end NFY_NBN_LateInvariant
-- END copied NBN_LateInvariant
-- BEGIN copied NBN_EncoderDomains: lean/NBN_EncoderDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_EncoderDomains
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem late (s : Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    AspisS6OuterEncodeSuccess.late_ready
      (fromPoolV1PairLatePublicStatementV1 (common s).lane_transition) := by
  intro output size
  obtain ⟨run,len⟩ := NFY_NBN_LateInvariant.statement_ready s valid output size
  refine ⟨NFY_NBN_LateTail.value (common s).lane_transition NFY_NBN_LateResult.header,?_,len⟩
  rw [late_call,run]
  rfl

theorem transfer (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) = ok (.Ok ())) :
    ∃ bytes, nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 p) = ok (.Ok bytes) := by
  obtain ⟨bytes,run,_⟩ := NFY_NBN_StatementDomains.payment_reached (.PrivateTransfer c p) valid
  change pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p = ok (.Ok bytes) at run
  refine ⟨bytes,?_⟩
  rw [transfer_call,run]
  rfl

theorem withdrawal (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) = ok (.Ok ())) :
    ∃ bytes, nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 p) = ok (.Ok bytes) := by
  obtain ⟨bytes,run,_⟩ := NFY_NBN_StatementDomains.payment_reached (.Withdrawal c p) valid
  change pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes) at run
  refine ⟨bytes,?_⟩
  rw [withdrawal_call,run]
  rfl

theorem validator (s : Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 s) = ok (.Ok ()) := by
  rw [validate_call,valid]
  rfl

#print axioms late
#print axioms transfer
#print axioms withdrawal
#print axioms validator
end NFY_NBN_EncoderDomains
-- END copied NBN_EncoderDomains
-- BEGIN copied NBN_EncoderBytes: lean/NBN_EncoderBytes.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_EncoderBytes
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

def tag : Statement → U8
  | .PrivateTransfer _ _ => 1#u8
  | .Withdrawal _ _ => 2#u8

def commonBytes (s : Statement) : List U8 :=
  AspisS6OuterByteLayout.common_prefix (fromPoolV1PairForestTerminalCommonV1 (common s)) (tag s)

def bytes (s : Statement) (pay : Array U8 216#usize) : Array U8 1880#usize :=
  ⟨(commonBytes s ++ (NFY_NBN_LateTail.value (common s).lane_transition NFY_NBN_LateResult.header).val) ++ pay.val, by
    have p := AspisS6OuterByteLayout.common_length (fromPoolV1PairForestTerminalCommonV1 (common s)) (tag s)
    have l := (NFY_NBN_LateInvariant.value_length (common s).lane_transition NFY_NBN_LateResult.header).trans NFY_NBN_LateResult.header_length
    have q := pay.property
    change pay.val.length = 216 at q
    change (NFY_NBN_LateTail.value (common s).lane_transition NFY_NBN_LateResult.header).val.length = 1520 at l
    change (commonBytes s).length = 144 at p
    simp only [List.length_append,p,l,q]
    rfl⟩

theorem length (s : Statement) (pay : Array U8 216#usize) : (bytes s pay).val.length = 1880 :=
  (bytes s pay).property

#print axioms length
end NFY_NBN_EncoderBytes
-- END copied NBN_EncoderBytes
-- BEGIN copied NBN_EncoderContents: lean/NBN_EncoderContents.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_EncoderContents
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem private_contents (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) = ok (.Ok ())) :
    ∃ pay : Array U8 216#usize,
      payment (.PrivateTransfer c p) = ok (.Ok pay) ∧
      AspisS6OuterNativeInstalled.encode (.PrivateTransfer c p) =
        ok (.Ok (NFY_NBN_EncoderBytes.bytes (.PrivateTransfer c p) pay)) := by
  have good := AspisS6OuterEncoderContents.private_contents
    (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1PrivateTransferPublicV1 p)
    (NFY_NBN_EncoderDomains.validator (.PrivateTransfer c p) valid) (NFY_NBN_EncoderDomains.late (.PrivateTransfer c p) valid)
    (NFY_NBN_EncoderDomains.transfer c p valid)
  obtain ⟨r,run,encoded,initial,updated,pay,success,size,len,late_run,pay_run,layout⟩ := WP.spec_imp_exists good
  cases success
  have late_call := AspisS6OuterNativeOps.late_call c.lane_transition initial
  have ready := (NFY_NBN_LateInvariant.statement_ready (.PrivateTransfer c p) valid initial size).1
  change pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 c.lane_transition initial =
    ok (.Ok (),NFY_NBN_LateTail.value c.lane_transition NFY_NBN_LateResult.header) at ready
  change nativeOps.late (fromPoolV1PairLatePublicStatementV1 c.lane_transition) initial = ok (.Ok (),updated) at late_run
  rw [ready] at late_call
  rw [late_call] at late_run
  simp only [resultMap,rustMapError] at late_run
  have same : NFY_NBN_LateTail.value c.lane_transition NFY_NBN_LateResult.header = updated :=
    congrArg Prod.snd (Result.ok.inj late_run)
  have pay_call := AspisS6OuterNativeOps.transfer_return p
  rw [pay_run] at pay_call
  change ok (.Ok pay) = pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p at pay_call
  have bytes_equal : encoded = NFY_NBN_EncoderBytes.bytes (.PrivateTransfer c p) pay := by
    apply Subtype.ext
    rw [layout,← same]
    rfl
  refine ⟨pay,pay_call.symm,?_⟩
  unfold AspisS6OuterNativeInstalled.encode
  change resultMap _ (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps
    (.PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1PrivateTransferPublicV1 p))) = _
  rw [run,bytes_equal]
  rfl

theorem withdrawal_contents (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) = ok (.Ok ())) :
    ∃ pay : Array U8 216#usize,
      payment (.Withdrawal c p) = ok (.Ok pay) ∧
      AspisS6OuterNativeInstalled.encode (.Withdrawal c p) =
        ok (.Ok (NFY_NBN_EncoderBytes.bytes (.Withdrawal c p) pay)) := by
  have good := AspisS6OuterEncoderContents.withdrawal_contents
    (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1WithdrawalPublicV1 p)
    (NFY_NBN_EncoderDomains.validator (.Withdrawal c p) valid) (NFY_NBN_EncoderDomains.late (.Withdrawal c p) valid)
    (NFY_NBN_EncoderDomains.withdrawal c p valid)
  obtain ⟨r,run,encoded,initial,updated,pay,success,size,len,late_run,pay_run,layout⟩ := WP.spec_imp_exists good
  cases success
  have late_call := AspisS6OuterNativeOps.late_call c.lane_transition initial
  have ready := (NFY_NBN_LateInvariant.statement_ready (.Withdrawal c p) valid initial size).1
  change pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 c.lane_transition initial =
    ok (.Ok (),NFY_NBN_LateTail.value c.lane_transition NFY_NBN_LateResult.header) at ready
  change nativeOps.late (fromPoolV1PairLatePublicStatementV1 c.lane_transition) initial = ok (.Ok (),updated) at late_run
  rw [ready] at late_call
  rw [late_call] at late_run
  simp only [resultMap,rustMapError] at late_run
  have same : NFY_NBN_LateTail.value c.lane_transition NFY_NBN_LateResult.header = updated :=
    congrArg Prod.snd (Result.ok.inj late_run)
  have pay_call := AspisS6OuterNativeOps.withdrawal_return p
  rw [pay_run] at pay_call
  change ok (.Ok pay) = pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p at pay_call
  have bytes_equal : encoded = NFY_NBN_EncoderBytes.bytes (.Withdrawal c p) pay := by
    apply Subtype.ext
    rw [layout,← same]
    rfl
  refine ⟨pay,pay_call.symm,?_⟩
  unfold AspisS6OuterNativeInstalled.encode
  change resultMap _ (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps
    (.Withdrawal (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1WithdrawalPublicV1 p))) = _
  rw [run,bytes_equal]
  rfl

#print axioms private_contents
#print axioms withdrawal_contents
end NFY_NBN_EncoderContents
-- END copied NBN_EncoderContents
-- BEGIN copied NBN_EncoderRejection: lean/NBN_EncoderRejection.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_EncoderRejection
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem source (s : Statement) (e : NFY_NBN_StatementResult.Error)
    (reject : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Err e)) :
    AspisS6OuterNativeInstalled.encode s = ok (.Err e) := by
  have v : nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 s) =
      ok (.Err (fromPoolV1PairForestTerminalFormatErrorV1 e)) := by
    rw [validate_call,reject]
    rfl
  unfold AspisS6OuterNativeInstalled.encode
    AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1
  rw [v]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp [resultMap,rustMapError,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,to_fromPoolV1PairForestTerminalFormatErrorV1]

#print axioms source
end NFY_NBN_EncoderRejection
-- END copied NBN_EncoderRejection
-- BEGIN copied NBN_EncoderResult: lean/NBN_EncoderResult.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_EncoderResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
open pool_v1.pair_forest_terminal

def result (s : Statement) : Result (core.result.Result (Array U8 1880#usize) NFY_NBN_StatementResult.Error) := do
  let validated ← NFY_NBN_StatementResult.result s
  match validated with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let pay ← payment s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok bytes => ok (.Ok (NFY_NBN_EncoderBytes.bytes s bytes))

theorem source (s : Statement) : AspisS6OuterNativeInstalled.encode s = result s := by
  obtain ⟨v,valid⟩ := AspisS6NativeForestTotal.validate_total s
  have modeled : NFY_NBN_StatementResult.result s = ok v := by rw [← NFY_NBN_StatementResult.source];exact valid
  cases v with
  | Err e =>
    rw [NFY_NBN_EncoderRejection.source s e valid]
    simp only [result,modeled,bind_tc_ok]
  | Ok unit =>
    cases unit
    have contents : ∃ pay, payment s = ok (.Ok pay) ∧
        AspisS6OuterNativeInstalled.encode s = ok (.Ok (NFY_NBN_EncoderBytes.bytes s pay)) := by
      cases s with
      | PrivateTransfer c p => exact NFY_NBN_EncoderContents.private_contents c p valid
      | Withdrawal c p => exact NFY_NBN_EncoderContents.withdrawal_contents c p valid
    obtain ⟨pay,payment_run,encoded⟩ := contents
    rw [encoded]
    simp only [result,modeled,bind_tc_ok,payment_run]

#print axioms source
end NFY_NBN_EncoderResult
-- END copied NBN_EncoderResult
-- BEGIN copied NBK_DeployedCallbackSelection: lean/NBK_DeployedCallbackSelection.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBK_DeployedCallbackSelection
open AspisR1

/-- The coherent installed SDK retains these slots from its input adapter.
This is a selection audit, not a native association or an installation. -/
theorem registry {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op25 = c.adapter.op25 ∧
    (DrvC_Installation.sdk c).op26 = c.adapter.op26 ∧
    (DrvC_Installation.sdk c).op27 = c.adapter.op27 ∧
    (DrvC_Installation.sdk c).op28 = c.adapter.op28 ∧
    (DrvC_Installation.sdk c).op29 = c.adapter.op29 ∧
    (DrvC_Installation.sdk c).op30 = c.adapter.op30 ∧
    (DrvC_Installation.sdk c).op31 = c.adapter.op31 ∧
    (DrvC_Installation.sdk c).op32 = c.adapter.op32 ∧
    (DrvC_Installation.sdk c).op33 = c.adapter.op33 ∧
    (DrvC_Installation.sdk c).op34 = c.adapter.op34 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem policy_accounts {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op15 = c.adapter.op15 ∧
    (DrvC_Installation.sdk c).op48 = c.adapter.op48 ∧
    (DrvC_Installation.sdk c).op49 = c.adapter.op49 := ⟨rfl,rfl,rfl⟩

#print axioms registry
#print axioms policy_accounts
end NFY_NBK_DeployedCallbackSelection
-- END copied NBK_DeployedCallbackSelection
-- BEGIN copied NBN_InstalledEncoder: lean/NBN_InstalledEncoder.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_InstalledEncoder
open Aeneas Aeneas.Std Result
open AspisR1
open AspisS6OuterNativeOps AspisS6CurrentAdapterCarrier

theorem source {F E : Type} (c : DrvC_Installation.Configuration F E)
    (s : AspisS6CurrentCodecInstallation.Statement) :
    (DrvC_Installation.sdk c).op22 s =
      resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1)
        (NFY_NBN_EncoderResult.result (toPoolV1PairForestTerminalStatementV1 s)) := by
  change AspisS6CurrentCodecInstallation.encode s = _
  unfold AspisS6CurrentCodecInstallation.encode
  rw [NFY_NBN_EncoderResult.source]

#print axioms source
end NFY_NBN_InstalledEncoder
-- END copied NBN_InstalledEncoder
-- BEGIN copied NBN_StatementEncoderSummary: lean/NBN_StatementEncoderSummary.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_StatementEncoderSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult NFY_NBN_ValidatorSummary
attribute [local instance] Classical.propDecidable
abbrev Raw := NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw
abbrev BytesResult := Result (core.result.Result (List U8) NFY_NBN_StatementResult.Error)

def prefixBytes (s : Statement) (anchor : Array U8 32#usize) : List U8 :=
  let c := AspisS6OuterCarrierBridge.fromPoolV1PairForestTerminalCommonV1 (common s)
  AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC.val ++
    [AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION,
     NFY_NBN_EncoderBytes.tag s,
     AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,c.output_lane] ++
    c.master_account.val ++ c.checkpoint_account.val ++ c.selected_lane_account.val ++
    (core.num.U64.to_le_bytes c.checkpoint_sequence).val ++ anchor.val

theorem prefix_source (s : Statement) :
    prefixBytes s (AspisR1.S2K.DigestBytes.bytes (common s).historical_global_anchor) = NFY_NBN_EncoderBytes.commonBytes s := by
  unfold prefixBytes NFY_NBN_EncoderBytes.commonBytes AspisS6OuterByteLayout.common_prefix
  rw [AspisS6NativeAfterstateEncoderReuse.native_digest_bytes]
  rfl

def observe (r : Result (core.result.Result (Array U8 1880#usize) NFY_NBN_StatementResult.Error)) : BytesResult := do
  let r ← r
  match r with
  | .Err e => ok (.Err e)
  | .Ok a => ok (.Ok a.val)

def run (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) (s : Statement) : BytesResult := do
  let valid ← NFY_NBN_ValidatorSummary.run enc t w s
  match valid with
  | .Err e => ok (.Err e)
  | .Ok _ =>
    let anchor ← enc (common s).historical_global_anchor
    let (status,late) ← NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero
    match status with
    | .Err e => ok (.Err (.LaneTransition e))
    | .Ok _ =>
      let pay ← paymentWith t w s
      match pay with
      | .Err e => ok (.Err (.Payment e))
      | .Ok a => ok (.Ok ((prefixBytes s anchor ++ late.val) ++ a.val))

theorem source (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (hd : Raw enc) (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    run enc t w s = observe (AspisS6OuterNativeInstalled.encode s) := by
  have hc : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc := fun d _ => hd d
  obtain ⟨v,hv⟩ := AspisS6NativeForestTotal.validate_total s
  have validation := NFY_NBN_ValidatorSummary.source enc t w hc ht hw s
  rw [hv] at validation
  cases v with
  | Err e =>
    rw [NFY_NBN_EncoderRejection.source s e hv]
    simp only [run,validation,observe,bind_tc_ok]
  | Ok u =>
    cases u
    obtain ⟨pay,hpay,_⟩ := NFY_NBN_StatementDomains.payment_reached s hv
    have late := (NFY_NBN_LateInvariant.statement_ready s hv NFY_NBN_LateResult.zero (by
      simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate];rfl)).1
    have contents : AspisS6OuterNativeInstalled.encode s = ok (.Ok (NFY_NBN_EncoderBytes.bytes s pay)) := by
      rw [NFY_NBN_EncoderResult.source]
      simp only [NFY_NBN_EncoderResult.result,← NFY_NBN_StatementResult.source,hv,hpay,bind_tc_ok]
    simp only [run,validation,bind_tc_ok]
    rw [hd _,NFY_NBN_LateSummary.source enc hc,late]
    simp only [bind_tc_ok]
    rw [payment_source t w ht hw s,hpay]
    simp only [bind_tc_ok]
    rw [prefix_source,contents]
    rfl

#print axioms prefix_source
#print axioms source
end NFY_NBN_StatementEncoderSummary
-- END copied NBN_StatementEncoderSummary
-- BEGIN copied NBN_AfterDecodeTypes: lean/NBN_AfterDecodeTypes.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecodeTypes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Digest := Array U32 8#usize
abbrev Decode := Array U8 32#usize → Result (core.result.Result Digest atomic_statement.AtomicStatementError)
def NBN_Dep_DigestDecode (decode : Decode) : Prop :=
  ∀ bytes, decode bytes = atomic_statement.decode_digest_canonical bytes
end NFY_NBN_AfterDecodeTypes
-- END copied NBN_AfterDecodeTypes
-- BEGIN copied NBN_AfterDecode16: lean/NBN_AfterDecode16.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecode16
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s19 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 560#usize, «end» := 592#usize }
  let r51 ← pool_v1.pair_terminal.exact 32#usize s19
  let cf34 ← core.result.Result.Insts.CoreOpsTry.branch r51
  match cf34 with
  | core.ops.control_flow.ControlFlow.Continue val34 =>
    let r52 ← decode val34
    let r53 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r52 ()
    let cf35 ← core.result.Result.Insts.CoreOpsTry.branch r53
    match cf35 with
    | core.ops.control_flow.ControlFlow.Continue val35 =>
      let s20 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 592#usize, «end» := 624#usize }
      let r54 ← pool_v1.pair_terminal.exact 32#usize s20
      let cf36 ← core.result.Result.Insts.CoreOpsTry.branch r54
      match cf36 with
      | core.ops.control_flow.ControlFlow.Continue val36 =>
        let r55 ← decode val36
        let r56 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r55 ()
        let cf37 ← core.result.Result.Insts.CoreOpsTry.branch r56
        match cf37 with
        | core.ops.control_flow.ControlFlow.Continue val37 =>
          let s21 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 624#usize, «end» := 656#usize }
          let r57 ← pool_v1.pair_terminal.exact 32#usize s21
          let cf38 ← core.result.Result.Insts.CoreOpsTry.branch r57
          match cf38 with
          | core.ops.control_flow.ControlFlow.Continue val38 =>
            let r58 ← decode val38
            let r59 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r58 ()
            let cf39 ← core.result.Result.Insts.CoreOpsTry.branch r59
            match cf39 with
            | core.ops.control_flow.ControlFlow.Continue val39 =>
              let s22 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 656#usize, «end» := 688#usize }
              let r60 ← pool_v1.pair_terminal.exact 32#usize s22
              let cf40 ← core.result.Result.Insts.CoreOpsTry.branch r60
              match cf40 with
              | core.ops.control_flow.ControlFlow.Continue val40 =>
                let r61 ← decode val40
                let r62 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r61 ()
                let cf41 ← core.result.Result.Insts.CoreOpsTry.branch r62
                match cf41 with
                | core.ops.control_flow.ControlFlow.Continue val41 =>
                  let s23 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 8#usize, «end» := 16#usize }
                  let r63 ← pool_v1.pair_terminal.exact 8#usize s23
                  let cf42 ← core.result.Result.Insts.CoreOpsTry.branch r63
                  match cf42 with
                  | core.ops.control_flow.ControlFlow.Continue val42 =>
                    let i6 ← lift (core.num.U64.from_le_bytes val42)
                    let r64 ← pool_v1.pair_terminal.validate_verified_afterstate { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) }
                    let cf43 ← core.result.Result.Insts.CoreOpsTry.branch r64
                    match cf43 with
                    | core.ops.control_flow.ControlFlow.Continue _ => ok (core.result.Result.Ok { next_pair_index := i6, next_root := val1, next_frontier := (Array.make 20#usize [ val3, val5, val7, val9, val11, val13, val15, val17, val19, val21, val23, val25, val27, val29, val31, val33, val35, val37, val39, val41 ]) })
                    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 = AspisS6NativeAfterstateDecoderFactored.part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_16
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NFY_NBN_AfterDecode16
-- END copied NBN_AfterDecode16
-- BEGIN copied NBN_AfterDecode12: lean/NBN_AfterDecode12.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecode12
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s15 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 432#usize, «end» := 464#usize }
  let r39 ← pool_v1.pair_terminal.exact 32#usize s15
  let cf26 ← core.result.Result.Insts.CoreOpsTry.branch r39
  match cf26 with
  | core.ops.control_flow.ControlFlow.Continue val26 =>
    let r40 ← decode val26
    let r41 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r40 ()
    let cf27 ← core.result.Result.Insts.CoreOpsTry.branch r41
    match cf27 with
    | core.ops.control_flow.ControlFlow.Continue val27 =>
      let s16 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 464#usize, «end» := 496#usize }
      let r42 ← pool_v1.pair_terminal.exact 32#usize s16
      let cf28 ← core.result.Result.Insts.CoreOpsTry.branch r42
      match cf28 with
      | core.ops.control_flow.ControlFlow.Continue val28 =>
        let r43 ← decode val28
        let r44 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r43 ()
        let cf29 ← core.result.Result.Insts.CoreOpsTry.branch r44
        match cf29 with
        | core.ops.control_flow.ControlFlow.Continue val29 =>
          let s17 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 496#usize, «end» := 528#usize }
          let r45 ← pool_v1.pair_terminal.exact 32#usize s17
          let cf30 ← core.result.Result.Insts.CoreOpsTry.branch r45
          match cf30 with
          | core.ops.control_flow.ControlFlow.Continue val30 =>
            let r46 ← decode val30
            let r47 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r46 ()
            let cf31 ← core.result.Result.Insts.CoreOpsTry.branch r47
            match cf31 with
            | core.ops.control_flow.ControlFlow.Continue val31 =>
              let s18 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 528#usize, «end» := 560#usize }
              let r48 ← pool_v1.pair_terminal.exact 32#usize s18
              let cf32 ← core.result.Result.Insts.CoreOpsTry.branch r48
              match cf32 with
              | core.ops.control_flow.ControlFlow.Continue val32 =>
                let r49 ← decode val32
                let r50 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r49 ()
                let cf33 ← core.result.Result.Insts.CoreOpsTry.branch r50
                match cf33 with
                | core.ops.control_flow.ControlFlow.Continue val33 =>
                  NFY_NBN_AfterDecode16.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 = AspisS6NativeAfterstateDecoderFactored.part_12 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NFY_NBN_AfterDecode16.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_12
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NFY_NBN_AfterDecode12
-- END copied NBN_AfterDecode12
-- BEGIN copied NBN_AfterDecode08: lean/NBN_AfterDecode08.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_AfterDecode08
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NFY_NBN_AfterDecodeTypes

def run (decode : Decode) (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array aspis_core.field.M31 8#usize) : Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1) := do
  let s11 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 304#usize, «end» := 336#usize }
  let r27 ← pool_v1.pair_terminal.exact 32#usize s11
  let cf18 ← core.result.Result.Insts.CoreOpsTry.branch r27
  match cf18 with
  | core.ops.control_flow.ControlFlow.Continue val18 =>
    let r28 ← decode val18
    let r29 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r28 ()
    let cf19 ← core.result.Result.Insts.CoreOpsTry.branch r29
    match cf19 with
    | core.ops.control_flow.ControlFlow.Continue val19 =>
      let s12 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 336#usize, «end» := 368#usize }
      let r30 ← pool_v1.pair_terminal.exact 32#usize s12
      let cf20 ← core.result.Result.Insts.CoreOpsTry.branch r30
      match cf20 with
      | core.ops.control_flow.ControlFlow.Continue val20 =>
        let r31 ← decode val20
        let r32 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r31 ()
        let cf21 ← core.result.Result.Insts.CoreOpsTry.branch r32
        match cf21 with
        | core.ops.control_flow.ControlFlow.Continue val21 =>
          let s13 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 368#usize, «end» := 400#usize }
          let r33 ← pool_v1.pair_terminal.exact 32#usize s13
          let cf22 ← core.result.Result.Insts.CoreOpsTry.branch r33
          match cf22 with
          | core.ops.control_flow.ControlFlow.Continue val22 =>
            let r34 ← decode val22
            let r35 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r34 ()
            let cf23 ← core.result.Result.Insts.CoreOpsTry.branch r35
            match cf23 with
            | core.ops.control_flow.ControlFlow.Continue val23 =>
              let s14 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 400#usize, «end» := 432#usize }
              let r36 ← pool_v1.pair_terminal.exact 32#usize s14
              let cf24 ← core.result.Result.Insts.CoreOpsTry.branch r36
              match cf24 with
              | core.ops.control_flow.ControlFlow.Continue val24 =>
                let r37 ← decode val24
                let r38 ← core.result.Result.map_err pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairVerifierTransportErrorV1 r37 ()
                let cf25 ← core.result.Result.Insts.CoreOpsTry.branch r38
                match cf25 with
                | core.ops.control_flow.ControlFlow.Continue val25 =>
                  NFY_NBN_AfterDecode12.run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25
                | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
              | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
            | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
          | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
        | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
      | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
    | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 (core.convert.FromSame pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) residual

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    (bytes : Slice U8) (val1 val3 val5 val7 val9 val11 val13 val15 val17 : Array aspis_core.field.M31 8#usize) :
    run decode bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 = AspisS6NativeAfterstateDecoderFactored.part_8 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 := by
  have same : decode = atomic_statement.decode_digest_canonical := funext lower
  unfold run
  simp only [NFY_NBN_AfterDecode12.source decode lower]
  rw [same]
  unfold AspisS6NativeAfterstateDecoderFactored.part_8
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms source
end NFY_NBN_AfterDecode08
-- END copied NBN_AfterDecode08

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
