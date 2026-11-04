import Lean
import NFY_Part040
import NFY_Part036
import RPz7_S6NativeForestHelpersV1
import RPz7_S6NativeDigestAcceptedInverseV1
import NFY_Part034
import Aeneas

-- BEGIN copied JFs_PublicLane: lean/JFs_PublicLane.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicLane
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_accounts

theorem encoded : atomic_statement.encode_digest_canonical NFY_JFt_Digest44.value=
    ok NFY_JFs_PaymentDigests.bytes44 :=
  AspisS6NativeDigestAcceptedInverse.accepted_inverse _ _ NFY_JFs_PaymentDigests.decode44

theorem source : pool_v1_pair_forest_output_lane_v1 NFY_JFt_Digest44.value=ok (.Ok 3#u8) := by
  unfold pool_v1_pair_forest_output_lane_v1
  rw [AspisS6NativeForestHelpers.canonical_eq,NFY_JFu_DigestCheck.source _ NFY_JFt_Digest44.canonical]
  simp only [bind_tc_ok,Bool.true_eq,↓reduceIte]
  unfold first_canonical_byte
  rw [encoded]
  rfl

#print axioms encoded
#print axioms source
end AspisR1.NFY_JFs_PublicLane
-- END copied JFs_PublicLane
-- BEGIN copied JFs_PublicValidation: lean/JFs_PublicValidation.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_PublicValidation
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 NFY_JFs_PublicValue.value=ok (.Ok ()) := by
  obtain ⟨encoded,contents,payment⟩:=NFY_JFs_PublicEncoders.payment
  obtain ⟨updated,late,length⟩:=NFY_JFs_PublicEncoders.late
  have common : PoolV1PairForestTerminalStatementV1.common NFY_JFs_PublicValue.value=ok NFY_JFs_PublicValue.common := by rfl
  have publicCall : statement_public_common NFY_JFs_PublicValue.value=
      ok (NFY_JFs_PaymentValue.common.pool,NFY_JFs_PaymentValue.common.deployment_domain,
        NFY_JFs_PaymentValue.common.anchor_sequence,NFY_JFs_PaymentValue.common.anchor_root,
        NFY_JFs_PaymentValue.common.nullifier,NFY_JFs_PaymentValue.common.asset_id) := by rfl
  have laneCall : pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      NFY_JFs_PaymentValue.common.nullifier=ok (.Ok 3#u8) := NFY_JFs_PublicLane.source
  unfold validate_pool_v1_pair_forest_terminal_statement_v1
  rw [common]
  simp only [bind_tc_ok,NFY_JFs_PublicValue.master_nonzero,NFY_JFs_PublicValue.checkpoint_nonzero,
    NFY_JFs_PublicValue.lane_nonzero,Bool.false_eq_true,↓reduceIte,lift,NFY_JFs_PublicComparisons.lane_bound]
  rw [show NFY_JFs_PublicValue.value=.PrivateTransfer NFY_JFs_PublicValue.common NFY_JFs_PaymentValue.value from rfl]
  simp only [payment,bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  dsimp only [NFY_JFs_PublicValue.value] at publicCall
  rw [publicCall]
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        s.startsWith "AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1" &&
          (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  try simp (config := { zeta := true, iota := true }) only
  simp only [uncurry,bind_tc_ok,NFY_JFs_PublicComparisons.pool,NFY_JFs_PublicComparisons.domain,
    NFY_JFs_PublicComparisons.snapshot_pool,NFY_JFs_PublicComparisons.anchor,NFY_JFs_PublicComparisons.sequence,
    Bool.false_eq_true,↓reduceIte,laneCall,
    AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,NFY_JFs_PublicComparisons.lane]
  simp only [uncurry,Array.to_slice_mut,lift,bind_tc_ok]
  try simp (config := { zeta := true, iota := true }) only
  have lateCall : pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
      NFY_JFs_PublicValue.common.lane_transition (Array.to_slice (Array.repeat 1520#usize 0#u8))=
      ok (.Ok (),updated) := late
  rw [lateCall]
  simp only [uncurry,bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]

#print axioms source
end AspisR1.NFY_JFs_PublicValidation
-- END copied JFs_PublicValidation
-- BEGIN copied JHb_Emit: lean/JHb_Emit.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_Emit
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open S2K
/-- Frozen emit_result control flow with an explicit return-data syscall and
its state. Field construction and codecs are the source S2K definitions.
This is a source model; native syscall/artifact association is not asserted. -/
def source {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement) :
    Result (core.result.Result (S2I.ReturnData.State A E) AdapterRw.solana_program_error.ProgramError) := do
  let result := ResultAdmission.value statement
  let validated ← validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement result
  match validated with
  | .Err _ => ok (.Err .InvalidInstructionData)
  | .Ok () =>
    let encoded ← encode_pool_v1_pair_forest_terminal_result_v1 result
    match encoded with
    | .Err _ => ok (.Err .InvalidInstructionData)
    | .Ok bytes =>
      if bytes.val.length ≠ 792 then ok (.Err .InvalidInstructionData)
      else if bytes.val.take 4 ≠ [65#u8,83#u8,82#u8,56#u8] then ok (.Err .InvalidInstructionData)
      else do
        let state' ← syscall state bytes.val
        ok (.Ok state')

theorem accepted {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall)
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ())) :
    source syscall state statement=ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes statement).val)) := by
  unfold source
  dsimp only
  rw [ResultBinding.validated statement valid,bind_tc_ok]
  rw [ResultPayload.encoded statement valid,bind_tc_ok]
  dsimp only
  rw [if_neg (by exact not_not_intro (ResultPayload.bytes statement).property)]
  rw [if_neg (by exact not_not_intro (ResultHeader.magic statement))]
  rw [runtime,bind_tc_ok]
#print axioms accepted

theorem real {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall) (state : S2I.ReturnData.State A E) :
    source syscall state NFY_JFs_PublicValue.value=
      ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes NFY_JFs_PublicValue.value).val)) :=
  accepted syscall runtime state _ NFY_JFs_PublicValidation.source
#print axioms real
end AspisR1.NFY_JHb_Emit
end
-- END copied JHb_Emit
-- BEGIN copied JHd_Discriminant: lean/JHd_Discriminant.lean

/-! Aeneas discriminant readers with enum-qualified instance names for import unions.
The pinned generator supplies both commands; only its anonymous instance name
is changed. Scalar types, explicit tags, generic binders and reader bodies are
preserved. This adapter must be rebuilt when the Aeneas generator is repinned. -/
open Lean Elab Term Meta
open Lean.Parser.Term Lean.Parser.Command

namespace NFY_JHd_Discriminant

syntax (name := JHdNamedDiscriminant) "JHd_discriminant" ident ("["num,*"]")? : attr

initialize JHdNamedDiscriminantAttribute : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    «name» := `JHdNamedDiscriminant,
    descr := "Emit the Aeneas reader with an enum-qualified instance name",
    add := fun declName stx _ => do
      let (ty, values) ← match stx with
        | `(attr| JHd_discriminant $ty) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty, none)
        | `(attr| JHd_discriminant $ty [$xs,*]) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty,
            some ((xs.getElems.toList.map Syntax.isNatLit?).map Option.get!))
        | _ => throwUnsupportedSyntax
      liftCommandElabM do
        let cmds ← Lean.Elab.Command.liftTermElabM
          (Aeneas.Discriminant.generateReadDiscriminantCmds declName ty values)
        Lean.Elab.Command.elabCommand cmds[0]!
        let instName := mkIdent (declName ++ `instDiscriminant)
        let id ← `(Parser.Command.declId| $instName:ident)
        let inst := cmds[1]!.rewriteBottomUp fun node => Id.run do
          if node.isOfKind ``Lean.Parser.Command.instance then
            return node.setArg 3 (mkNullNode #[id.raw])
          return node
        if inst == cmds[1]! then
          throwError "Pinned Aeneas generator no longer emits an instance command"
        Lean.Elab.Command.elabCommand inst
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

end NFY_JHd_Discriminant
-- END copied JHd_Discriminant
-- BEGIN copied JHd_RequestTypes: lean/JHd_RequestTypes.lean
-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [aspis_statement]: type definitions
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

namespace AspisR20Request

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32

/-- [aspis_statement::atomic_statement::AtomicStatementError]
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 62:0-70:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive atomic_statement.AtomicStatementError where
| NonCanonicalDigest : atomic_statement.AtomicStatementError
| NonCanonicalAssetId : atomic_statement.AtomicStatementError
| FeeOutOfRange : atomic_statement.AtomicStatementError
| PathDepthMismatch : atomic_statement.AtomicStatementError
| InsertionIndexOutOfRange : atomic_statement.AtomicStatementError
| CurrentAnchorMismatch : atomic_statement.AtomicStatementError
| OutputAnchorMismatch : atomic_statement.AtomicStatementError

/-- [aspis_statement::pool_v1::pair_forest_terminal::asq8_payment_reference::CommonPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/asq8_payment_reference.rs', lines 20:0-27:1 -/
structure pool_v1.pair_forest_terminal.asq8_payment_reference.CommonPublicV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31

/-- [aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 46:0-55:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient_commitment : Array aspis_core.field.M31 8#usize
  change_commitment : Array aspis_core.field.M31 8#usize

/-- [aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 58:0-68:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  amount : Std.U32
  destination_token_account : Array Std.U8 32#usize
  change_commitment : Array aspis_core.field.M31 8#usize

/-- [aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind]
    Source: 'crates/aspis-statement/src/pool_v1/historical_anchor.rs', lines 32:0-35:1
    Visibility: public -/
@[JHd_discriminant u8 [1,2]]
inductive pool_v1.historical_anchor.PoolV1TransitionKind where
| PrivateTransfer : pool_v1.historical_anchor.PoolV1TransitionKind
| Withdrawal : pool_v1.historical_anchor.PoolV1TransitionKind

/-- [aspis_statement::pool_v1::payment_relation::CommonPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 168:0-175:1 -/
structure pool_v1.payment_relation.CommonPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31

/-- [aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 128:0-143:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.payment_relation.PoolV1PaymentStatementFormatError where
| WrongLength : pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongMagic : pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongVersion : pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongTransitionKind :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongDigestEncoding :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonZeroReserved : pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| ZeroRequiredBinding :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidAnchorSequence :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonCanonicalDigest :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonCanonicalAssetId :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidWithdrawalAmount :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidDestination :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidEnvelope : pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| EnvelopeMismatch : pool_v1.payment_relation.PoolV1PaymentStatementFormatError

/-- [aspis_statement::pool_v1::incremental_merkle::PoolV1TreeError]
    Source: 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs', lines 32:0-46:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.incremental_merkle.PoolV1TreeError where
| TreeFull : pool_v1.incremental_merkle.PoolV1TreeError
| InsufficientCapacity : pool_v1.incremental_merkle.PoolV1TreeError
| IndexOutOfRange : pool_v1.incremental_merkle.PoolV1TreeError
| RootMismatch : pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalFrontier : pool_v1.incremental_merkle.PoolV1TreeError
| WrongLength : pool_v1.incremental_merkle.PoolV1TreeError
| WrongMagic : pool_v1.incremental_merkle.PoolV1TreeError
| WrongVersion : pool_v1.incremental_merkle.PoolV1TreeError
| WrongDepth : pool_v1.incremental_merkle.PoolV1TreeError
| WrongTreeHash : pool_v1.incremental_merkle.PoolV1TreeError
| WrongDigestEncoding : pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalDigest : pool_v1.incremental_merkle.PoolV1TreeError
| NonZeroReserved : pool_v1.incremental_merkle.PoolV1TreeError

/-- [aspis_statement::pool_v1::pair_forest_accounts::PoolV1PairForestAccountErrorV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs', lines 96:0-118:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 where
| WrongLength : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongMagic : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongVersion : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongLaneCount : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongDigestEncoding :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongDepth : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongFormatBinding :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| NonZeroReserved : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| ZeroRequiredBinding :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidBoolean : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidMasterState :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidLane : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneMasterMismatch :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneOrderMismatch :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneSequenceDecreased :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| DuplicateCheckpoint :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| CheckpointSequenceOverflow :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| NonCanonicalDigest :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Identity : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Policy : pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Tree :
  pool_v1.incremental_merkle.PoolV1TreeError →
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalPaymentV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 71:0-74:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1 where
| PrivateTransfer :
  pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
| Withdrawal :
  pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalRequestV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 63:0-68:1
    Visibility: public -/
structure pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 where
  verifier_profile : Array Std.U8 32#usize
  verifier_release : Array Std.U8 32#usize
  pool_program : Array Std.U8 32#usize
  «public» : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotErrorV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 438:0-448:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 where
| WrongLength : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongMagic : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongVersion : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongFormatBinding : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| NonZeroReserved : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| ZeroRequiredBinding : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| SequenceIndexMismatch :
  pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| TreeFull : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| NonCanonicalDigest : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

/-- [aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 56:0-72:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 where
| WrongLength : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongMagic : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongVersion : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongStatementVersion :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongDigestEncoding :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidTransitionKind :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongSuccessCode : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongPairFormat : pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| ZeroRequiredBinding :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidProofBodyLength :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidStatementPayloadLength :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidLiveSnapshotPayloadLength :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| NonCanonicalOutputPair :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidAfterstateIndex :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| NonCanonicalAfterstate :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementErrorV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 422:0-435:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 where
| WrongLength : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongMagic : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongVersion : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongItemCount :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongHeaderLength :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongSnapshotLength :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongAfterstateLength :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongTotalLength :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| NonZeroReserved :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| Snapshot :
  pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 →
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| Afterstate :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| AfterstateIndexMismatch :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 179:0-202:1
    Visibility: public -/
@[JHd_discriminant isize]
inductive pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  where
| WrongLength :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongMagic :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongVersion :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongDigestEncoding :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| InvalidTransitionKind :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| InvalidOutputLane :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| NonZeroBinding :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| NonCanonicalDigest :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| OutputLaneMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| MasterBindingMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| DeploymentBindingMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| HistoricalAnchorMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| CheckpointBindingMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| SelectedLaneBindingMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| LiveSnapshotMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| CandidateAfterstateMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| ResultBindingMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WithdrawalDestinationMismatch :
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Payment :
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| LaneTransition :
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Afterstate :
  pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Account :
  pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 →
  pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_request_reference_v1::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 491:25-491:78 -/
@[reducible]
def pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::encode_pool_v1_pair_forest_terminal_request_reference_v1::closure]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 485:25-485:78 -/
@[reducible]
def pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_request_reference_v1.closure
  :=
Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 442:17-442:74 -/
@[reducible]
def pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1 :=
Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 419:17-419:67 -/
@[reducible]
def pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure :=
Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_common::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 370:17-370:74 -/
@[reducible]
def pool_v1.payment_relation.decode_common.closure_1 := Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_common::closure]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 366:17-366:74 -/
@[reducible]
def pool_v1.payment_relation.decode_common.closure := Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#2]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 408:17-408:74 -/
@[reducible]
def pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2
  :=
Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 404:17-404:74 -/
@[reducible]
def pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1
  :=
Unit

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 382:17-382:67 -/
@[reducible]
def pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_reference_v1::closure#4]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 562:21-562:75 -/
@[reducible]
def pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_reference_v1::closure#3]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 559:21-559:75 -/
@[reducible]
def pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_reference_v1::closure#2]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 556:21-556:75 -/
@[reducible]
def pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_reference_v1::closure#1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 550:25-550:78 -/
@[reducible]
def pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1
  :=
Unit

/-- [aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_request_reference_v1::closure]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 545:29-545:82 -/
@[reducible]
def pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure
  :=
Unit

end AspisR20Request
-- END copied JHd_RequestTypes
-- BEGIN copied JHd_RequestExternal: lean/JHd_RequestExternal.lean

/-! P6 library interface for std slice/array equality. Rust 1.93 implements
this using `as_array`; the pinned Charon cannot lower its pointer cast. This
model delegates to the existing Aeneas slice/slice comparator after the
array-to-slice coercion. Kani's slice_array_header_comparison_model checks eq
and ne for every four-byte header and every input length 0..320. The codec
only uses this interface for four-byte magic headers. No new axiom. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace Slice.Insts.CoreCmpPartialEqArray

def eq {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.eq cmp s a.to_slice

def ne {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.ne cmp s a.to_slice

#print axioms eq
#print axioms ne
end Slice.Insts.CoreCmpPartialEqArray
-- END copied JHd_RequestExternal

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
