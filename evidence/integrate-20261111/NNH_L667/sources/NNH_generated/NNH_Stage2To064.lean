import NNH_Stage2HeadPort
import NNH_CorrectReads
import NNH_CorrectCallInputs
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2To064
open Aeneas Aeneas.Std Result AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

def continuation (ops : Ops) (statement : LIBB_PoolCarriers.Statement)
 (pub proof ck : Slice U8) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
 let reply ← ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) pub proof ck () none
 let mapped ← core.result.Result.map_err (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError) reply ops.op44
 let cf ← core.result.Result.Insts.CoreOpsTry.branch mapped
 match cf with
 | .Continue _ => ops.op53 statement
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual

theorem source (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (p : NNH_CorrectTx2Inputs.Packet missing env err reserve program xs data clock) :
 ∃ segment,RSL.TX2_241.Dom064 V0 (bytes p.encoded.to_slice,bytes segment,bytes p.checkpoint) ∧
 LIBB_Tx2EnvCode.code env p.encoded.to_slice segment p.checkpoint=.ok (.Ok ()) ∧
 r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data clock=
 continuation (NNH_CorrectConfiguration.sdk missing env err reserve) p.validated.statement p.encoded.to_slice segment p.checkpoint := by
 obtain ⟨segment,range,domain,auth⟩ := NNH_CorrectCallInputs.produce missing env err reserve program xs data clock p
 obtain ⟨proof_size,checkpoint_size,validated_size⟩ := NNH_CorrectExtents.value missing env err reserve program xs data clock p
 have native_size : Slice.len p.proof=58295#usize := by
  apply UScalar.eq_of_val_eq
  change p.proof.val.length=58295
  exact proof_size
 have late : (NNH_CorrectConfiguration.sdk missing env err reserve).op19=.ok 1520#usize := rfl
 have statement_eq := congrArg RSL.TX2_242.Validated.statement p.validated_eq
 change p.validated.statement=p.logical.cut.validated.statement at statement_eq
 have encode : (NNH_CorrectConfiguration.sdk missing env err reserve).op22 p.validated.statement=.ok (.Ok p.encoded) := by
  rw [statement_eq]
  exact p.encode
 refine ⟨segment,domain,auth,?_⟩
 rw [NNH_Stage2HeadPort.source missing env err reserve program xs data clock p,
  NNH_CorrectReads.source missing env err reserve program xs data clock p,
  NNH_Stage2Suffix.source _ _ _ _ _ _ native_size validated_size late encode range]
 simp only [observer,bind_tc_ok]
 rfl
#print axioms source
end NNH_Stage2To064
