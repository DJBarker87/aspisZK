import NNH_ValidateTailPort
import LIBB_ScannerExtent
set_option autoImplicit false
noncomputable section
namespace NNH_ValidatedExtent
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (instruction : Slice U8)
 (clock : Except RSL.ProgramError UInt64) (out : RSL.TX2_242.Validated L)
 (success : NNH_ValidateEval.value L D LIBB_PoolLib.values ⟨key program,accounts xs,bytes instruction,clock⟩ env=.ok out) :
 out.proof_length=RSL.PROOF_BYTES := by
 obtain ⟨packet⟩ := NNH_ValidateCut.produce L D LIBB_PoolLib.values _ env out success
 obtain ⟨proof,head,proof_eq⟩ := NNH_AccountHeadOk.value xs packet.proof packet.head
 have data_ok := packet.data_ok
 rw [←proof_eq] at data_ok
 obtain ⟨data,read,data_eq⟩ := NNH_GetterOk.value base env proof packet.data data_ok
 have scan_ok := packet.scan_ok
 rw [←data_eq] at scan_ok
 obtain ⟨scanned,source,after_eq,len_eq⟩ := NNH_PoolValuePorts.scan_ok data packet.scanned.1 packet.scanned.2 scan_ok
 have extent := NMS_R2N_ScanScalar.proof_value data scanned source
 rw [packet.output]
 exact len_eq.symm.trans extent
#print axioms value
end NNH_ValidatedExtent
