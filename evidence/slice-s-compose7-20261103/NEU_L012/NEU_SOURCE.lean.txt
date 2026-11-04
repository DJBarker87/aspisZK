import NEU_ReconstructAdopted
set_option autoImplicit false
noncomputable section
namespace NEU_CallDomains
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
open NEU_ReconstructCore
inductive Call where
  | common : Auth → Candidate → Call
  | transfer : Common → payment_relation.PoolV1PrivateTransferPublicV1 → Call
  | withdrawal : Common → payment_relation.PoolV1WithdrawalPublicV1 → Call

def calls (request : Request) (a : Auth) (c : Candidate) : List Call :=
  if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
    if a.master.identity.asset_id=NDM_CohortReconstruction.requested request then
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
    NED_ReconstructCarriers.toRawCommon
      (NED_ReconstructCarriers.fromRawCommon (common a c)) = common a c :=
  NED_RawCarrierInverses.common _

theorem transfer_packet (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1) :
    NED_ReconstructCarriers.toRaw
      (NED_ReconstructCarriers.fromRaw (.PrivateTransfer c p)) = .PrivateTransfer c p :=
  NED_RawCarrierInverses.statement _

theorem withdrawal_packet (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1) :
    NED_ReconstructCarriers.toRaw
      (NED_ReconstructCarriers.fromRaw (.Withdrawal c p)) = .Withdrawal c p :=
  NED_RawCarrierInverses.statement _

def ReplyRange (s : NEU_BoxModel.Statement)
    (r : core.result.Result NEU_BoxModel.Statement NEU_BoxModel.ProgramError) : Prop :=
  r=.Ok s ∨ r=.Err .InvalidInstructionData

theorem transfer_reply_range (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1) :
    ∃ r, r1_pool_adapter.transfer_statement_box c p=ok r ∧ ReplyRange (.PrivateTransfer c p) r := by
  refine ⟨NEU_BoxModel.wrap _ (NEU_BoxModel.status _),NEU_BoxModel.transfer c p,?_⟩
  cases NEU_BoxModel.status (.PrivateTransfer c p) <;> simp only [NEU_BoxModel.wrap,ReplyRange,or_true,true_or]

theorem withdrawal_reply_range (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1) :
    ∃ r, r1_pool_adapter.withdrawal_statement_box c p=ok r ∧ ReplyRange (.Withdrawal c p) r := by
  refine ⟨NEU_BoxModel.wrap _ (NEU_BoxModel.status _),NEU_BoxModel.withdrawal c p,?_⟩
  cases NEU_BoxModel.status (.Withdrawal c p) <;> simp only [NEU_BoxModel.wrap,ReplyRange,or_true,true_or]

#print axioms reached_domains
#print axioms common_packet
#print axioms transfer_packet
#print axioms withdrawal_packet
#print axioms transfer_reply_range
#print axioms withdrawal_reply_range
end NEU_CallDomains
