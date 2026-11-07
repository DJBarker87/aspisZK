import NNH_Tx2ConcreteInputs
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Extents
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : core.result.Result U64 solana_program_error.ProgramError)
 (p : NNH_Tx2ConcreteInputs.Packet missing env err reserve program xs data clock) :
 p.proof.val.length=58295 ∧ p.checkpoint.val.length=1768 ∧ p.validated.proof_length=57607#usize := by
 have proof := p.logical.cut.proof_length
 rw [←p.proof_eq,p.extent] at proof
 have ck := p.logical.domain.2.1
 rw [←p.checkpoint_eq] at ck
 refine ⟨?_,?_,?_⟩
 · simpa only [bytes,List.length_map,RSL.AFTERSTATE_BYTES,RSL.PROOF_BYTES] using proof
 · simpa only [bytes,List.length_map,RSL.CHECKPOINT_BYTES] using ck
 · apply UScalar.eq_of_val_eq
   have eq := congrArg RSL.TX2_242.Validated.proof_length p.validated_eq
   change p.validated.proof_length.val=p.logical.cut.validated.proof_length at eq
   exact eq.trans p.extent
#print axioms value
end NNH_Stage2Extents
