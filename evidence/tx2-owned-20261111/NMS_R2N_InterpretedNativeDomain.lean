import NMS_R2N_GetterMeaning
import NMS_R2N_RSLInputOps
import NMS_R2N_RSLRanges
import NMS_R2Domains
import NMS_R2N_ScanScalar
set_option autoImplicit false
noncomputable section
namespace NMS_R2N_InterpretedNativeDomain
open Aeneas Aeneas.Std AdapterRw NMS_R2N_RSLScalars NMS_R2N_RSLPoolCarriers
/-- G1b domain transport at the ACTUAL typed 241 call triple. No coherent
library is fixed, and no unconditional Root0/checkpoint-extent clause is
introduced. All call equations are LOCAL source cuts, not root hypotheses. -/
theorem entered (V : RSL.TX2_241.V2Lib)
 (program : solana_pubkey.Pubkey) (accounts_ : Accounts) (instruction : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError)
 (domain : RSL.TX2_241.Domain V (args241 program accounts_ instruction slot))
 (acc0 acc6 : r1_pool_adapter.owned.OwnedAccount)
 (proofData checkpointData proof : Slice U8) (publicBytes : Aeneas.Std.Array U8 1880#usize)
 (length finish : Usize) (env : RSL.Env) (events0 events6 : List RSL.Event)
 (countGuard : (Slice.len accounts_ != 7#usize) = false)
 (index0 : Slice.index_usize accounts_ 0#usize = .ok acc0)
 (index6 : Slice.index_usize accounts_ 6#usize = .ok acc6)
 (read0 : NMS_R2N_GetterMeaning.meaning acc0 env ⟨.ret (.Ok proofData),events0⟩)
 (read6 : NMS_R2N_GetterMeaning.meaning acc6 env ⟨.ret (.Ok checkpointData),events6⟩)
 (checkpointChecked : (account acc6).length = .ok RSL.CHECKPOINT_BYTES)
 (scanExtent : length = 57607#usize)
 (checked : Usize.checked_add 688#usize length = some finish)
 (lengthGuard : (Slice.len proofData != finish) = false)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proofData ⟨688#usize,finish⟩ = .ok proof) :
 RSL.TX2_241.Dom064 V (bytes publicBytes.to_slice,bytes proof,bytes checkpointData) := by
 have count := NMS_R2N_RSLInputOps.count accounts_ countGuard
 have idx0 := NMS_R2N_RSLInputOps.index accounts_ 0#usize acc0 index0
 have idx6 := NMS_R2N_RSLInputOps.index accounts_ 6#usize acc6 index6
 simp only [NMS_R2N_RSLInputOps.zero_value] at idx0
 simp only [NMS_R2N_RSLInputOps.six_value] at idx6
 have interpreted0 := NMS_R2N_GetterMeaning.full acc0 env _ read0
 have stored0 := NMS_R2N_GeneralGetters.success (account acc0).bytes env (bytes proofData) events0 interpreted0
 have interpreted6 := NMS_R2N_GetterMeaning.full acc6 env _ read6
 have stored6 := NMS_R2N_GeneralGetters.success (account acc6).bytes env (bytes checkpointData) events6 interpreted6
 have finishValue := NLM_CheckedAddFacts.success 688#usize length finish checked
 rw [NMS_R2N_RSLInputOps.afterstate_value] at finishValue
 have proofLength := congrArg (fun x : Usize => x.val)
   (NLM_CheckedAddFacts.guard_eq proofData finish lengthGuard)
 have proofExtent : (bytes proofData).length = RSL.AFTERSTATE_BYTES + length.val := by
   rw [bytes_length]
   simpa only [Slice.len_val,finishValue] using proofLength
 have scanValue : length.val = RSL.PROOF_BYTES := by
   rw [scanExtent]
   exact NMS_R2N_ScanScalar.proof_bytes_value
 have dom := NMS_R2Domains.entered V _ domain (account acc0) (account acc6)
   (bytes proofData) (bytes checkpointData) (bytes publicBytes.to_slice)
   count idx0 idx6 stored0 stored6 checkpointChecked length.val scanValue proofExtent
   (NMS_R2N_RSLRanges.public_extent publicBytes)
 have ordered : (688#usize).val ≤ finish.val := by
   rw [NMS_R2N_RSLInputOps.afterstate_value,finishValue]
   exact Nat.le_add_right _ _
 have within : finish.val ≤ proofData.val.length := by
   have h := congrArg (fun x : Usize => x.val)
     (NLM_CheckedAddFacts.guard_eq proofData finish lengthGuard)
   simpa only [Slice.len_val] using Nat.le_of_eq h.symm
 have selected := NMS_R2N_RSLRanges.selected proofData proof 688#usize finish ordered within range
 rw [NMS_R2N_RSLInputOps.afterstate_value,finishValue] at selected
 rw [selected]
 exact dom
#print axioms entered
end NMS_R2N_InterpretedNativeDomain
