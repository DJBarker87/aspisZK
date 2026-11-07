import NNH_CorrectExtents
import NNH_SliceRangeOk
import NNH_CommonResumeDomain
set_option autoImplicit false
noncomputable section
namespace NNH_CorrectCallInputs
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem produce (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (p : NNH_CorrectTx2Inputs.Packet missing env err reserve program xs data clock) :
 ∃ segment,core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) p.proof ⟨688#usize,58295#usize⟩=.ok segment ∧
 RSL.TX2_241.Dom064 V0 (bytes p.encoded.to_slice,bytes segment,bytes p.checkpoint) ∧
 LIBB_Tx2EnvCode.code env p.encoded.to_slice segment p.checkpoint=.ok (.Ok ()) := by
 obtain ⟨proof_length,checkpoint_length,validated_length⟩ := NNH_CorrectExtents.value missing env err reserve program xs data clock p
 obtain ⟨segment,index,same⟩ := NNH_SliceRangeOk.value p.proof 688#usize 58295#usize (by scalar_tac) (by simp only [Slice.length]; rw [proof_length]; scalar_tac)
 have equal : bytes segment=RSL.slice p.logical.cut.proof_data RSL.AFTERSTATE_BYTES (RSL.AFTERSTATE_BYTES+p.logical.cut.validated.proof_length) := by
  rw [same,p.proof_eq,p.extent]
  rfl
 have domain := p.logical.domain
 rw [←p.public_eq,←equal,←p.checkpoint_eq] at domain
 have auth := p.logical.cut.auth_ok
 rw [←p.public_eq,←equal,←p.checkpoint_eq] at auth
 exact ⟨segment,index,domain,NNH_AuthCodeOk.code env _ _ _ auth⟩
#print axioms produce
end NNH_CorrectCallInputs
