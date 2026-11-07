import NNH_Stage2ResumeOccurrence
import NNH_Stage1NativePublic
import NNH_Stage1PrepareDomain
import NNH_ReservationOkBinding
set_option autoImplicit false
noncomputable section
namespace NNH_ExactRemainingTypes
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
/-- Unproved model-transport obligation, NOT an assumption of a shipped top.
The reservation equation is the existing host EnvRep conjunct. -/
def tx2Op11 : Prop :=
 ∀ (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation),
 NJC_FilledClause.reserved reserve=env.reservation →
 ∀ pub proof ck : Slice U8,
 RSL.TX2_241.Dom064 V0 (bytes pub,bytes proof,bytes ck) →
 LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ()) →
 (NNH_CorrectConfiguration.sdk missing env err reserve).op11
  (SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk missing env err reserve))
  pub proof ck () none=.ok (.Ok ())

/-- Unproved A1 Ok model transport; residual Missing is DATA, not a literal
host instance. This proposition is recorded only as the next exact target. -/
def tx1Ok : Prop :=
 ∀ (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation),
 NJC_FilledClause.reserved reserve=env.reservation →
 ∀ (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (saved : alloc.vec.Vec U8),
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ env=.ok (bytes saved.deref) →
 r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data=.ok (.Ok saved)

/-- Unproved A1 weak Err model transport. Error payload equality is not added. -/
def tx1Err : Prop :=
 ∀ (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation),
 NJC_FilledClause.reserved reserve=env.reservation →
 ∀ (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (error : RSL.ProgramError),
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ env=.error error →
 ∃ pe,r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data=.ok (.Err pe)

#print axioms tx2Op11
#print axioms tx1Ok
#print axioms tx1Err
end NNH_ExactRemainingTypes
