import SCE_FixtureBank
import SCE_FixtureWrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureRead
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store SCE_FixtureData
open S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint SCE_FixtureBank

theorem loaded : CPG_Projection.loaded observations true 2 = some (MultiproofConeCanonical.bytesOf saved.val) := by
  change CPR_DataPersistence.visible (CPR_DataPersistence.snapshot final 2) = _
  change (if final.lamports 2 = 0 then none else
    some (MultiproofConeCanonical.bytesOf (final.cells 2).data.val)) = _
  rw [final_balance]
  change some (MultiproofConeCanonical.bytesOf (final.cells 2).data.val) = _
  rw [final_data]
  rfl

theorem reader_checkpoint : (e2.buffers 2).val = saved.val := by
  change ((cached final).cells 2).data.val = saved.val
  change (if final.lamports 2 = 0 then (⟨[],by simp⟩ : Slice U8) else (final.cells 2).data).val = saved.val
  rw [final_balance]
  change (final.cells 2).data.val = saved.val
  exact congrArg (fun d : Slice U8 => d.val) final_data

theorem written_checkpoint :
    payloadBytes encode (SCE_FixtureWrappers.post1.payload (e1.heap.accounts 2).1) 1768 =
      MultiproofConeCanonical.bytesOf saved.val := by
  unfold SCE_FixtureWrappers.post1
  rw [S2W_EntryWriteHistory.written_bytes encode e1.heap 2 0 0 (source (nativeBytes saved))
    rfl rfl (by exact SCE_FixtureShape.size_before)]
  have size : (nativeBytes saved).length = 1768 := by
    rw [nativeBytes,List.length_map,SCE_FixtureShape.size_saved]
  rw [← size,source_bytes,vector_representation]

#print axioms loaded
#print axioms reader_checkpoint
#print axioms written_checkpoint
end AspisR1.SCE_FixtureRead
end
