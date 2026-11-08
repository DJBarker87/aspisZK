import NNY_Stage2Residual
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_Stage2PacketResidual
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
/-- The remaining native obligation at the SAME packet/segment. All original
Dom064, source success and emit facts are outputs from the returned reference.
This equivalence does not inhabit NND_A2. -/
theorem returned (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (program : _root_.AdapterRw.solana_pubkey.Pubkey)
 (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 _root_.AdapterRw.solana_program_error.ProgramError)
 (o : RSL.Obs (Except RSL.ProgramError Unit))
 (ref : RSL.TX2_241.Ref L D V0 ⟨key program,accounts xs,bytes data,reply slot clock⟩ env o)
 (ret : o.exit=.ret (.ok ())) :
 ∃ p : NNH_CorrectTx2Inputs.Packet m env err r program xs data clock,
 ∃ segment,
 RSL.TX2_241.Dom064 V0 (bytes p.encoded.to_slice,bytes segment,bytes p.checkpoint) ∧
 LIBB_Tx2EnvCode.code env p.encoded.to_slice segment p.checkpoint=ok (.Ok ()) ∧
 (_root_.AdapterRw.r1_pool_adapter.owned.stage2_owned (NNH_CorrectConfiguration.sdk m env err r)
   program xs data clock=ok (.Ok ()) ↔
  (NNH_CorrectConfiguration.sdk m env err r).op11
   (_root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
   p.encoded.to_slice segment p.checkpoint () none=ok (.Ok ())) := by
 obtain ⟨p,segment,domain,auth,source,emit⟩ := NNU_Stage2Tail.returnedCuts m env err r program xs data clock o ref ret
 refine ⟨p,segment,domain,auth,?_⟩
 rw [source]
 exact NNY_Stage2Residual.continuation_iff _ _ _ _ _ emit
#print axioms returned
end AspisR1.NNY_Stage2PacketResidual
end
