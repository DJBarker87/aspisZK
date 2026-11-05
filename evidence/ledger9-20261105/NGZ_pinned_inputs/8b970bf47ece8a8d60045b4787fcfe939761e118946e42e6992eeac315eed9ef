import Lean
import NFY_Part056
import NFY_Part052
import NDM_SnapshotRef.Funs
import NFY_Part032

-- BEGIN copied NDM_CohortGate: evidence/native-front4b-20261028/NDM_CohortGate.lean
set_option autoImplicit false
namespace NFY_NDM_CohortGate
open Aeneas Aeneas.Std Result
abbrev RawOptionEq (i : core.cmp.PartialEq U64 U64) := AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption i
abbrev RawFieldEq := AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31

theorem option_reference (live next : U64) :
 (do let o ← lift (U64.checked_add live 1#u64)
     core.cmp.PartialEq.ne.trait_default (RawOptionEq core.cmp.PartialEqU64) o (some next)) =
 (do let accepted ← NDM_GateRef.next_gate_ref live next
     ok (!accepted)) := by
 unfold NDM_GateRef.next_gate_ref
 cases call : U64.checked_add live 1#u64 <;>
  simp [lift,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
   RawOptionEq,AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption,
   AspisR1AdapterReconstruct.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
   core.cmp.PartialEqU64,liftFun2,core.cmp.impls.PartialEqU64.eq,
   AspisR1AdapterReconstruct.optionDiscriminantInst,
   AspisR1AdapterReconstruct.optionDiscriminant,read_discriminant]

theorem field_reference (x y : U32) :
 core.cmp.PartialEq.ne.trait_default RawFieldEq x y=ok (decide (x≠y)) := by
 by_cases h : x=y
 · subst y
   simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    RawFieldEq,AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
 · simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    RawFieldEq,AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    AspisR1AdapterReconstruct.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,h]

theorem option_natural (live next : U64) :
 (do let o ← lift (U64.checked_add live 1#u64)
     core.cmp.PartialEq.ne.trait_default (RawOptionEq core.cmp.PartialEqU64) o (some next)) =
 ok (!(decide (live.val+1=next.val))) := by
 rw [option_reference live next,NFY_NDM_GateTotal.reference]
 rfl

#print axioms option_reference
#print axioms field_reference
#print axioms option_natural
end NFY_NDM_CohortGate
-- END copied NDM_CohortGate
-- BEGIN copied NDM_CohortConstructors: evidence/native-front4b-20261028/NDM_CohortConstructors.lean
set_option autoImplicit false
namespace NFY_NDM_CohortConstructors
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Validation := core.result.Result Unit pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def wrap (s : Statement) (r : Validation) : core.result.Result Statement solana_program_error.ProgramError :=
 match r with | .Ok _=>.Ok s | .Err _=>.Err .InvalidInstructionData

/-- The exact emitted constructor, including uniform error erasure, against
 the SAME actual emitted validator call. No native opaque validator is discharged. -/
theorem transfer (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1)
 (reply : Validation)
 (sameCall : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.PrivateTransfer c p)=ok reply) :
 r1_pool_adapter.transfer_statement_box c p=ok (wrap (.PrivateTransfer c p) reply) := by
 unfold r1_pool_adapter.transfer_statement_box
 rw [sameCall]
 cases reply <;> rfl

theorem withdrawal (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1)
 (reply : Validation)
 (sameCall : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.Withdrawal c p)=ok reply) :
 r1_pool_adapter.withdrawal_statement_box c p=ok (wrap (.Withdrawal c p) reply) := by
 unfold r1_pool_adapter.withdrawal_statement_box
 rw [sameCall]
 cases reply <;> rfl

#print axioms transfer
#print axioms withdrawal
end NFY_NDM_CohortConstructors
-- END copied NDM_CohortConstructors
-- BEGIN copied NDM_CohortReconstruction: evidence/native-front4b-20261028/NDM_CohortReconstruction.lean
set_option autoImplicit false
namespace NFY_NDM_CohortReconstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1
abbrev Request := pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1

def requested (request : Request) : U32 := match request.public with
 | .PrivateTransfer p=>p.asset_id
 | .Withdrawal p=>p.asset_id

def finish (request : Request) (a : Auth) (c : Candidate) := do
 let common ← r1_pool_adapter.asq8_common a c
 match request.public with
 | .PrivateTransfer p=>r1_pool_adapter.transfer_statement_box common p
 | .Withdrawal p=>r1_pool_adapter.withdrawal_statement_box common p

def direct (request : Request) (a : Auth) (c : Candidate) :=
 if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
  if a.master.identity.asset_id=requested request then finish request a c
  else ok (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData)
 else ok (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)

theorem word_cond {T : Type} (x y : U32) (a b : T) :
 (if x.val=y.val then a else b)=(if x=y then a else b) := by
 have eqv : x.val=y.val ↔ x=y := ⟨UScalar.eq_of_val_eq,congrArg (fun z : U32=>z.val)⟩
 by_cases h : x=y <;> simp_all

/-- Actual emitted reconstruction control with actual emitted constructors,
 valid for every input. This is model-only; K082 gives no native gate credit. -/
theorem control (request : Request) (a : Auth) (c : Candidate) :
 r1_pool_adapter.reconstruct_asq8_statement request a c=direct request a c := by
 have gate := NFY_NDM_CohortGate.option_natural a.live_snapshot.next_pair_index c.next_pair_index
 simp only [lift,bind_tc_ok] at gate
 unfold r1_pool_adapter.reconstruct_asq8_statement
 simp only [lift,bind_tc_ok]
 rw [gate]
 simp only [bind_tc_ok]
 cases request with
 | mk profile release program payment=>
  cases payment <;>
   by_cases step : a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val <;>
   simp [direct,finish,requested,step,NFY_NDM_CohortGate.field_reference] <;>
   exact word_cond _ _ _ _

#print axioms word_cond
#print axioms control
end NFY_NDM_CohortReconstruction
-- END copied NDM_CohortReconstruction
-- BEGIN copied NEU_ReconstructCore: evidence/slice-s-compose7-20261103/NEU_ReconstructCore.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_ReconstructCore
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
abbrev Request := pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def common (a : Auth) (c : Candidate) : Common :=
  { master_account := a.master_account, checkpoint_account := a.checkpoint_account,
    selected_lane_account := a.selected_lane_account, output_lane := a.selected_lane.lane_id,
    checkpoint_sequence := a.checkpoint.checkpoint_sequence,
    historical_global_anchor := a.checkpoint.global_root,
    lane_transition := {live_snapshot := a.live_snapshot, candidate_afterstate := c} }

theorem common_result (a : Auth) (c : Candidate) :
    r1_pool_adapter.asq8_common a c = ok (common a c) := rfl

def run {State : Type} (request : Request) (a : Auth) (c : Candidate) (state : State) :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NFY_NDM_CohortReconstruction.requested request then
      match request.public with
      | .PrivateTransfer p => NFY_NEU_BoxModel.run (.PrivateTransfer (common a c) p) state
      | .Withdrawal p => NFY_NEU_BoxModel.run (.Withdrawal (common a c) p) state
    else (ok (.Err solana_program_error.ProgramError.InvalidInstructionData),state,[])
  else (ok (.Err solana_program_error.ProgramError.InvalidAccountData),state,[])

def trace (request : Request) (a : Auth) (c : Candidate) :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NFY_NDM_CohortReconstruction.requested request then
      match request.public with
      | .PrivateTransfer p => (NFY_NED_ValidatorTrace.run
          (NFY_NED_ReconstructCarriers.fromRaw (.PrivateTransfer (common a c) p))).2
      | .Withdrawal p => (NFY_NED_ValidatorTrace.run
          (NFY_NED_ReconstructCarriers.fromRaw (.Withdrawal (common a c) p))).2
    else []
  else []

/-- Model composition at the exact source calls. Constructor child hypotheses
are discharged by NFY_NEU_BoxModel; native auth/common/Box associations remain
separate certificate obligations, never premises hidden in this theorem. -/
theorem result_state_effects {State : Type} (request : Request) (a : Auth)
    (c : Candidate) (state : State) :
    run request a c state =
      (r1_pool_adapter.reconstruct_asq8_statement request a c,state,trace request a c) := by
  rw [NFY_NDM_CohortReconstruction.control]
  unfold run trace NFY_NDM_CohortReconstruction.direct
  by_cases gate : a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val
  · simp only [if_pos gate]
    by_cases asset : a.master.identity.asset_id=NFY_NDM_CohortReconstruction.requested request
    · simp only [if_pos asset]
      unfold NFY_NDM_CohortReconstruction.finish
      rw [common_result,bind_tc_ok]
      cases h : request.public with
      | PrivateTransfer p => exact NFY_NEU_BoxModel.transfer_result_state_effects (common a c) p state
      | Withdrawal p => exact NFY_NEU_BoxModel.withdrawal_result_state_effects (common a c) p state
    · simp only [if_neg asset]
  · simp only [if_neg gate]

#print axioms common_result
#print axioms result_state_effects
end NFY_NEU_ReconstructCore
-- END copied NEU_ReconstructCore
-- BEGIN copied NDM_StatementReference: evidence/native-front4b-20261028/NDM_StatementReference.lean
set_option autoImplicit false
namespace NFY_NDM_StatementReference
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := NFY_NDM_CommonCarrier.Common
abbrev Transfer := payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := payment_relation.PoolV1WithdrawalPublicV1
abbrev Validation := core.result.Result Unit pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def accepted (reply : Validation) : Bool := match reply with | .Ok _=>true | .Err _=>false

def lift {C P : Type} (build : C → P → Statement)
 (reply : core.result.Result (C × P) U8) : core.result.Result Statement solana_program_error.ProgramError :=
 match reply with | .Ok (c,p)=>.Ok (build c p) | .Err _=>.Err .InvalidInstructionData

def reference {C P : Type} (build : C → P → Statement) (c : C) (p : P) (valid : Bool) := do
 let reply ← NDM_SnapshotRef.validation_ref c p valid
 ok (lift build reply)

def call (ops : Ops) (statement : Statement) : Result
 (core.result.Result Statement solana_program_error.ProgramError) := do
 let reply ← ops.op21 statement
 ok (match reply with | .Ok _=>.Ok statement | .Err _=>.Err .InvalidInstructionData)

/-- Same constructed statement and SAME validator reply. The native callback
 association and its installed semantic interpretation remain separate obligations. -/
theorem transfer (ops : Ops) (c : Common) (p : Transfer) (reply : Validation)
 (sameCall : ops.op21 (.PrivateTransfer c p)=ok reply) :
 call ops (.PrivateTransfer c p) = reference (fun c p => (.PrivateTransfer c p : Statement)) c p (accepted reply) := by
 unfold call
 rw [sameCall]
 cases reply <;> rfl

theorem withdrawal (ops : Ops) (c : Common) (p : Withdrawal) (reply : Validation)
 (sameCall : ops.op21 (.Withdrawal c p)=ok reply) :
 call ops (.Withdrawal c p) = reference (fun c p => (.Withdrawal c p : Statement)) c p (accepted reply) := by
 unfold call
 rw [sameCall]
 cases reply <;> rfl

/-- Error payloads are discarded uniformly, not only for a fixture error variant. -/
theorem error_payload (ops : Ops) (statement : Statement)
 (error : pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
 (sameCall : ops.op21 statement=ok (.Err error)) :
 call ops statement=ok (.Err .InvalidInstructionData) := by
 unfold call
 rw [sameCall]
 rfl

#print axioms transfer
#print axioms withdrawal
#print axioms error_payload
end NFY_NDM_StatementReference
-- END copied NDM_StatementReference
-- BEGIN copied NDM_CohortStatement: evidence/native-front4b-20261028/NDM_CohortStatement.lean
set_option autoImplicit false
namespace NFY_NDM_CohortStatement
open Aeneas Aeneas.Std Result
open AspisR1.JHf_Carrier
abbrev RawStatement := NFY_NDM_CohortConstructors.Statement
abbrev RawReply := core.result.Result RawStatement AspisR1AdapterReconstruct.solana_program_error.ProgramError
abbrev Reply := core.result.Result NFY_NDM_StatementReference.Statement AdapterRw.solana_program_error.ProgramError

def transport (r : RawReply) : Reply := match r with
 | .Ok s=>.Ok (fromPoolV1PairForestTerminalStatementV1 s)
 | .Err e=>.Err (AspisR1.NFY_JHf_ProgramErrorCarrier.fromRaw e)

def accepted (r : NFY_NDM_CohortConstructors.Validation) : Bool :=
 match r with | .Ok _=>true | .Err _=>false

/-- Extracted safe reference to actual cohort constructor on the SAME actual
 validator invocation. The native validator abstraction remains OPEN. -/
theorem transfer (c : NFY_NDM_StatementReference.Common) (p : NFY_NDM_StatementReference.Transfer)
 (reply : NFY_NDM_CohortConstructors.Validation)
 (sameCall : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.PrivateTransfer (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1PrivateTransferPublicV1 p))=ok reply) :
 (do let r ← AspisR1AdapterReconstruct.r1_pool_adapter.transfer_statement_box
       (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1PrivateTransferPublicV1 p)
     ok (transport r))=
 NFY_NDM_StatementReference.reference (fun c p=>(.PrivateTransfer c p : NFY_NDM_StatementReference.Statement)) c p (accepted reply) := by
 rw [NFY_NDM_CohortConstructors.transfer _ _ reply sameCall]
 cases reply <;> rfl

theorem withdrawal (c : NFY_NDM_StatementReference.Common) (p : NFY_NDM_StatementReference.Withdrawal)
 (reply : NFY_NDM_CohortConstructors.Validation)
 (sameCall : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.Withdrawal (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1WithdrawalPublicV1 p))=ok reply) :
 (do let r ← AspisR1AdapterReconstruct.r1_pool_adapter.withdrawal_statement_box
       (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1WithdrawalPublicV1 p)
     ok (transport r))=
 NFY_NDM_StatementReference.reference (fun c p=>(.Withdrawal c p : NFY_NDM_StatementReference.Statement)) c p (accepted reply) := by
 rw [NFY_NDM_CohortConstructors.withdrawal _ _ reply sameCall]
 cases reply <;> rfl

#print axioms transfer
#print axioms withdrawal
end NFY_NDM_CohortStatement
-- END copied NDM_CohortStatement
-- BEGIN copied NDM_AdoptedReconstruction: evidence/native-front4b-20261028/NDM_AdoptedReconstruction.lean
set_option autoImplicit false
namespace NFY_NDM_AdoptedReconstruction
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.JHf_Carrier

/-- Control normalization of the existing op52 source selection, including
 its actual carrier/error conversion. No replacement dictionary is installed. -/
theorem selected (request : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1)
 (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : NFY_NDM_CommonCarrier.Candidate) :
 AspisR1.NFY_JHf_ReconstructionSlot.source request a c =
 (do let raw ← NFY_NDM_CohortReconstruction.direct (toRequest request)
       (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NFY_NDM_CohortStatement.transport raw)) := by
 unfold AspisR1.NFY_JHf_ReconstructionSlot.source
 rw [NFY_NDM_CohortReconstruction.control]
 cases call : NFY_NDM_CohortReconstruction.direct (toRequest request)
  (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) with
 | fail e=>rfl
 | div=>rfl
 | ok reply=>cases reply <;> rfl

#print axioms selected
end NFY_NDM_AdoptedReconstruction
-- END copied NDM_AdoptedReconstruction
-- BEGIN copied NEU_ReconstructAdopted: evidence/slice-s-compose7-20261103/NEU_ReconstructAdopted.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_ReconstructAdopted
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.JHf_Carrier
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := NFY_NDM_CommonCarrier.Candidate

def run {State : Type} (request : Request) (a : Auth) (c : Candidate) (state : State) :=
  let observed := NFY_NEU_ReconstructCore.run (toRequest request)
    (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) state
  ((do let reply ← observed.1; ok (NFY_NDM_CohortStatement.transport reply)),observed.2.1,observed.2.2)

/-- Exact selected op52 source, full Result, external state and ordered child
trace. All constructor validator hypotheses are discharged in the model.
This needs the separate native certificates to become a composed root. -/
theorem result_state_effects {State : Type} (request : Request) (a : Auth)
    (c : Candidate) (state : State) :
    run request a c state =
    (AspisR1.NFY_JHf_ReconstructionSlot.source request a c,state,
      NFY_NEU_ReconstructCore.trace (toRequest request) (toAuthenticatedAsq8Accounts a)
        (toPoolV1PairVerifiedAfterstateV1 c)) := by
  unfold run
  rw [NFY_NEU_ReconstructCore.result_state_effects]
  dsimp only
  unfold AspisR1.NFY_JHf_ReconstructionSlot.source
  cases call : AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (toRequest request) (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

#print axioms result_state_effects
end NFY_NEU_ReconstructAdopted
-- END copied NEU_ReconstructAdopted
-- BEGIN copied NEU_CallDomains: evidence/slice-s-compose7-20261103/NEU_CallDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_CallDomains
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
open NFY_NEU_ReconstructCore
inductive Call where
  | common : Auth → Candidate → Call
  | transfer : Common → payment_relation.PoolV1PrivateTransferPublicV1 → Call
  | withdrawal : Common → payment_relation.PoolV1WithdrawalPublicV1 → Call

def calls (request : Request) (a : Auth) (c : Candidate) : List Call :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NFY_NDM_CohortReconstruction.requested request then
      .common a c :: (match request.public with
        | .PrivateTransfer p => [.transfer (common a c) p]
        | .Withdrawal p => [.withdrawal (common a c) p])
    else []
  else []

theorem reached_domains (request : Request) (a : Auth) (c : Candidate) :
    (∀ a' c', Call.common a' c' ∈ calls request a c → a'=a ∧ c'=c) ∧
    (∀ d p, Call.transfer d p ∈ calls request a c →
      d=common a c ∧ request.public=.PrivateTransfer p) ∧
    (∀ d p, Call.withdrawal d p ∈ calls request a c →
      d=common a c ∧ request.public=.Withdrawal p) := by
  unfold calls
  split
  · split
    · cases h : request.public <;> simp [h]
    · simp
  · simp

theorem common_packet (a : Auth) (c : Candidate) :
    NFY_NED_ReconstructCarriers.toRawCommon
      (NFY_NED_ReconstructCarriers.fromRawCommon (common a c)) = common a c :=
  NFY_NED_RawCarrierInverses.common _

theorem transfer_packet (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1) :
    NFY_NED_ReconstructCarriers.toRaw
      (NFY_NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p)) = .PrivateTransfer c p :=
  NFY_NED_RawCarrierInverses.statement _

theorem withdrawal_packet (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1) :
    NFY_NED_ReconstructCarriers.toRaw
      (NFY_NED_ReconstructCarriers.fromRaw (.Withdrawal c p)) = .Withdrawal c p :=
  NFY_NED_RawCarrierInverses.statement _

def ReplyRange (s : NFY_NEU_BoxModel.Statement)
    (r : core.result.Result NFY_NEU_BoxModel.Statement NFY_NEU_BoxModel.ProgramError) : Prop :=
  r=.Ok s ∨ r=.Err .InvalidInstructionData

theorem transfer_reply_range (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1) :
    ∃ r, r1_pool_adapter.transfer_statement_box c p=ok r ∧ ReplyRange (.PrivateTransfer c p) r := by
  refine ⟨NFY_NEU_BoxModel.wrap _ (NFY_NEU_BoxModel.status _),NFY_NEU_BoxModel.transfer c p,?_⟩
  cases NFY_NEU_BoxModel.status (.PrivateTransfer c p) <;> simp only [NFY_NEU_BoxModel.wrap,ReplyRange,or_true,true_or]

theorem withdrawal_reply_range (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1) :
    ∃ r, r1_pool_adapter.withdrawal_statement_box c p=ok r ∧ ReplyRange (.Withdrawal c p) r := by
  refine ⟨NFY_NEU_BoxModel.wrap _ (NFY_NEU_BoxModel.status _),NFY_NEU_BoxModel.withdrawal c p,?_⟩
  cases NFY_NEU_BoxModel.status (.Withdrawal c p) <;> simp only [NFY_NEU_BoxModel.wrap,ReplyRange,or_true,true_or]

#print axioms reached_domains
#print axioms common_packet
#print axioms transfer_packet
#print axioms withdrawal_packet
#print axioms transfer_reply_range
#print axioms withdrawal_reply_range
end NFY_NEU_CallDomains
-- END copied NEU_CallDomains
-- BEGIN copied NEU_PublicProjections: evidence/slice-s-compose7-20261103/NEU_PublicProjections.lean
set_option autoImplicit false
namespace NFY_NEU_PublicProjections
open Aeneas Aeneas.Std
open AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation
abbrev Transfer := PoolV1PrivateTransferPublicV1
abbrev Withdrawal := PoolV1WithdrawalPublicV1

def get {α : Type} {n : Usize} (a : Array α n) (i : Fin n.val) : α :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

def transfer (p : Transfer) (slot : Fin 8) (i : Fin 8) (j : Fin 32) : Nat :=
  match slot.val with
  | 0 => (get p.pool j).val
  | 1 => (get p.deployment_domain j).val
  | 2 => p.anchor_sequence.val
  | 3 => (get p.anchor_root i).val
  | 4 => (get p.nullifier i).val
  | 5 => p.asset_id.val
  | 6 => (get p.change_commitment i).val
  | _ => (get p.recipient_commitment i).val

def withdrawal (p : Withdrawal) (slot : Fin 9) (i : Fin 8) (j : Fin 32) : Nat :=
  match slot.val with
  | 0 => (get p.pool j).val
  | 1 => (get p.deployment_domain j).val
  | 2 => p.anchor_sequence.val
  | 3 => (get p.anchor_root i).val
  | 4 => (get p.nullifier i).val
  | 5 => p.asset_id.val
  | 6 => (get p.change_commitment i).val
  | 7 => p.amount.val
  | _ => (get p.destination_token_account j).val

/-- Arbitrary native scalar/byte/word observation identifies the ENTIRE public
record; no unobserved array positions are zeroed or assumed equal. -/
theorem transfer_ext (p q : Transfer)
    (point : ∀ slot i j, transfer p slot i j=transfer q slot i j) : p=q := by
  have pool : p.pool=q.pool := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j
  have deployment : p.deployment_domain=q.deployment_domain := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j
  have sequence : p.anchor_sequence=q.anchor_sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have anchor : p.anchor_root=q.anchor_root := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ i ⟨0,by decide⟩
  have nullifier : p.nullifier=q.nullifier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ i ⟨0,by decide⟩
  have asset : p.asset_id=q.asset_id := by
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have change : p.change_commitment=q.change_commitment := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ i ⟨0,by decide⟩
  have recipient : p.recipient_commitment=q.recipient_commitment := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ i ⟨0,by decide⟩
  cases p; cases q
  congr 1 <;> assumption

theorem withdrawal_ext (p q : Withdrawal)
    (point : ∀ slot i j, withdrawal p slot i j=withdrawal q slot i j) : p=q := by
  have pool : p.pool=q.pool := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j
  have deployment : p.deployment_domain=q.deployment_domain := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j
  have sequence : p.anchor_sequence=q.anchor_sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have anchor : p.anchor_root=q.anchor_root := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ i ⟨0,by decide⟩
  have nullifier : p.nullifier=q.nullifier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ i ⟨0,by decide⟩
  have asset : p.asset_id=q.asset_id := by
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have change : p.change_commitment=q.change_commitment := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ i ⟨0,by decide⟩
  have amount : p.amount=q.amount := by
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have destination : p.destination_token_account=q.destination_token_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨8,by decide⟩ ⟨0,by decide⟩ j
  cases p; cases q
  congr 1 <;> assumption

#print axioms transfer_ext
#print axioms withdrawal_ext
end NFY_NEU_PublicProjections
-- END copied NEU_PublicProjections
-- BEGIN copied NEU_CommonProjections: evidence/slice-s-compose7-20261103/NEU_CommonProjections.lean
set_option autoImplicit false
namespace NFY_NEU_CommonProjections
open Aeneas Aeneas.Std
open NFY_NEU_PublicProjections (get)
abbrev Common := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def value (c : Common) (slot : Fin 15) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  match slot.val with
  | 0 => (get c.master_account j).val
  | 1 => (get c.checkpoint_account j).val
  | 2 => (get c.selected_lane_account j).val
  | 3 => c.output_lane.val
  | 4 => c.checkpoint_sequence.val
  | 5 => (get c.historical_global_anchor i).val
  | 6 => (get c.lane_transition.live_snapshot.pool j).val
  | 7 => (get c.lane_transition.live_snapshot.deployment_domain j).val
  | 8 => c.lane_transition.live_snapshot.sequence.val
  | 9 => c.lane_transition.live_snapshot.next_pair_index.val
  | 10 => (get c.lane_transition.live_snapshot.current_root i).val
  | 11 => (get (get c.lane_transition.live_snapshot.frontier k) i).val
  | 12 => c.lane_transition.candidate_afterstate.next_pair_index.val
  | 13 => (get c.lane_transition.candidate_afterstate.next_root i).val
  | _ => (get (get c.lane_transition.candidate_afterstate.next_frontier k) i).val

/-- One arbitrary field/byte/word/frontier projection identifies the complete
nested common record. No unread positions are fixed to fixture values. -/
theorem common_ext (c d : Common)
    (point : ∀ slot i j k, value c slot i j k=value d slot i j k) : c=d := by
  have h0 : c.master_account=d.master_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h1 : c.checkpoint_account=d.checkpoint_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h2 : c.selected_lane_account=d.selected_lane_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h3 : c.output_lane=d.output_lane := by
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h4 : c.checkpoint_sequence=d.checkpoint_sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h5 : c.historical_global_anchor=d.historical_global_anchor := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h6 : c.lane_transition.live_snapshot.pool=d.lane_transition.live_snapshot.pool := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h7 : c.lane_transition.live_snapshot.deployment_domain=d.lane_transition.live_snapshot.deployment_domain := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h8 : c.lane_transition.live_snapshot.sequence=d.lane_transition.live_snapshot.sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h9 : c.lane_transition.live_snapshot.next_pair_index=d.lane_transition.live_snapshot.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨9,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h10 : c.lane_transition.live_snapshot.current_root=d.lane_transition.live_snapshot.current_root := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨10,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h11 : c.lane_transition.live_snapshot.frontier=d.lane_transition.live_snapshot.frontier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro k
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨11,by decide⟩ i ⟨0,by decide⟩ k
  have h12 : c.lane_transition.candidate_afterstate.next_pair_index=d.lane_transition.candidate_afterstate.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨12,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h13 : c.lane_transition.candidate_afterstate.next_root=d.lane_transition.candidate_afterstate.next_root := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨13,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h14 : c.lane_transition.candidate_afterstate.next_frontier=d.lane_transition.candidate_afterstate.next_frontier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro k
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨14,by decide⟩ i ⟨0,by decide⟩ k
  cases c with
  | mk m0 ch0 sl0 l0 seq0 an0 lt0 =>
    cases lt0 with
    | mk live0 candidate0 =>
      cases live0
      cases candidate0
      cases d with
      | mk m1 ch1 sl1 l1 seq1 an1 lt1 =>
        cases lt1 with
        | mk live1 candidate1 =>
          cases live1
          cases candidate1
          simp_all only

#print axioms common_ext
end NFY_NEU_CommonProjections
-- END copied NEU_CommonProjections

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
