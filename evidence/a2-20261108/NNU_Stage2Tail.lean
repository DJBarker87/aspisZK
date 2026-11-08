import NNH_Stage2To064
import NNH_ReturnsBundle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_Stage2Tail
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem emitPacket (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (program : _root_.AdapterRw.solana_pubkey.Pubkey) (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 _root_.AdapterRw.solana_program_error.ProgramError)
 (p : NNH_CorrectTx2Inputs.Packet m env err r program xs data clock) :
 (NNH_CorrectConfiguration.sdk m env err r).op53 p.validated.statement=.ok (.Ok ()) := by
 have statement := congrArg RSL.TX2_242.Validated.statement p.validated_eq
 change p.validated.statement=p.logical.cut.validated.statement at statement
 change NNH_EmitModel.code p.validated.statement=.ok (.Ok ())
 apply NNH_EmitModel.ok
 rw [statement]
 exact p.logical.cut.emit_ok

theorem tail (ops : _root_.AdapterRw.Ops) (statement : LIBB_PoolCarriers.Statement) (pub proof ck : Slice U8)
 (call : ops.op11 (_root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) pub proof ck () none=.ok (.Ok ()))
 (emit : ops.op53 statement=.ok (.Ok ())) :
 NNH_Stage2To064.continuation ops statement pub proof ck=.ok (.Ok ()) := by
 unfold NNH_Stage2To064.continuation
 rw [call]
 simp only [bind_tc_ok,core.result.Result.map_err,Port4C_GeometryStd.mapError,core.result.Result.Insts.CoreOpsTry.branch,emit]

/-- Derive the SAME source cut and the completed tail port from a returned
canonical reference. The actual op11 call is still open, not a premise here. -/
theorem returnedCuts (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (program : _root_.AdapterRw.solana_pubkey.Pubkey) (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 _root_.AdapterRw.solana_program_error.ProgramError)
 (o : RSL.Obs (Except RSL.ProgramError Unit))
 (ref : RSL.TX2_241.Ref L D V0 ⟨key program,accounts xs,bytes data,reply slot clock⟩ env o)
 (ret : o.exit=.ret (.ok ())) :
 ∃ p : NNH_CorrectTx2Inputs.Packet m env err r program xs data clock,
 ∃ segment,
 RSL.TX2_241.Dom064 V0 (bytes p.encoded.to_slice,bytes segment,bytes p.checkpoint) ∧
 LIBB_Tx2EnvCode.code env p.encoded.to_slice segment p.checkpoint=.ok (.Ok ()) ∧
 _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk m env err r) program xs data clock=
 NNH_Stage2To064.continuation (NNH_CorrectConfiguration.sdk m env err r) p.validated.statement p.encoded.to_slice segment p.checkpoint ∧
 (NNH_CorrectConfiguration.sdk m env err r).op53 p.validated.statement=.ok (.Ok ()) := by
 have evaluated := (NNH_Stage2GuardedEval.returned _ env) o (.ok ()) ref ret
 obtain ⟨p⟩ := NNH_CorrectTx2Inputs.produce m env err r program xs data clock evaluated.symm
 obtain ⟨segment,domain,auth,source⟩ := NNH_Stage2To064.source m env err r program xs data clock p
 exact ⟨p,segment,domain,auth,source,emitPacket m env err r program xs data clock p⟩
#print axioms emitPacket
#print axioms tail
#print axioms returnedCuts
end AspisR1.NNU_Stage2Tail
end
