import NNH_ValidateCut
import NNH_ValidateScanStep
import NNH_AccountHeadOk
import NNH_ValidatedCarrier
import NNH_GetterOk
set_option autoImplicit false
noncomputable section
namespace NNH_ValidateTailPort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (instruction : Slice U8)
 (clock : Except RSL.ProgramError UInt64) (out : RSL.TX2_242.Validated L)
 (packet : NNH_ValidateCut.Packet L D LIBB_PoolLib.values ⟨key program,accounts xs,bytes instruction,clock⟩ env out)
 (nativeAuth : r1_pool_adapter.AuthenticatedAsq8Accounts) (auth_eq : auth nativeAuth=packet.auth) :
 ∃ native,NNH_ValidateFission.scan (NNH_Tx2ModelSlots.install base env) xs packet.request nativeAuth=.ok (.Ok native) ∧
 NNH_ValidatedCarrier.value native=out := by
 obtain ⟨proof,head,proof_eq⟩ := NNH_AccountHeadOk.value xs packet.proof packet.head
 have data_ok := packet.data_ok
 rw [←proof_eq] at data_ok
 obtain ⟨data,read,data_eq⟩ := NNH_GetterOk.value base env proof packet.data data_ok
 have scan_ok := packet.scan_ok
 rw [←data_eq] at scan_ok
 obtain ⟨scanned,scan,after_eq,len_eq⟩ := NNH_PoolValuePorts.scan_ok data packet.scanned.1 packet.scanned.2 scan_ok
 have reconstruct_ok := packet.reconstruct_ok
 rw [←auth_eq] at reconstruct_ok
 have reconstruct := NNH_ReconstructValuePort.ok packet.request nativeAuth packet.scanned.1 packet.statement reconstruct_ok
 rw [←after_eq] at reconstruct
 refine ⟨_,NNH_ValidateScanStep.source base env xs packet.request nativeAuth proof data scanned packet.statement head read scan reconstruct,?_⟩
 change (⟨packet.statement,scanned.proof_length.val⟩ : RSL.TX2_242.Validated L)=out
 rw [len_eq]
 exact packet.output.symm
#print axioms value
end NNH_ValidateTailPort
