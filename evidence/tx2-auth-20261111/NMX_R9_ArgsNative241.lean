import NMX_R9_HeaderFactor241
import NMS_R2N_RSLScalarEq
set_option autoImplicit false
noncomputable section
namespace NMX_R9_ArgsNative241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

def args (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.TX2_241.Args :=
 ⟨NMS_R2N_RSLScalars.b32 p,NMS_R2N_RSLPoolCarriers.accounts accounts,NMS_R2N_RSLScalars.bytes data,
 NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot⟩

theorem count (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 (Slice.len accounts != 7#usize) = ((NMS_R2N_RSLPoolCarriers.accounts accounts).length != 7) := by
 rw [NMS_R2N_RSLScalarEq.scalar_bne,NMX_R2_LengthGuard.value]
 simp only [NMS_R2N_RSLPoolCarriers.accounts,List.length_map]
 have seven : (7#usize).val = 7 := by scalar_tac
 rw [seven]
 by_cases same : accounts.val.length = 7 <;> simp [same]

#print axioms count
end NMX_R9_ArgsNative241
end
