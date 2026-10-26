import SCE_FixtureRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureVersion
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store SCE_FixtureData
open S2W_ReturnedCheckpoint S2W_EntryWriteHistory SCE_FixtureBank SCE_FixtureRead

theorem events : observations.physicalEvents false = [.rollback,.rollback,.rollback] :=
  congrArg Prod.snd result

/-- Constructed history for the SAME two accepted wrappers and physical events.
This model fixture does not assert extraction of n1/n2 to the cryptographic source. -/
def version : S2X.CheckpointVersionBinding
    (payloadBytes encode (SCE_FixtureWrappers.post1.payload (e1.heap.accounts 2).1) 1768)
    (MultiproofConeCanonical.bytesOf (e2.buffers (e2.handles 6).1).val) where
  key := 2
  ledger := byteLedger (CPR_SourceBank.afterCopy (cached initial) 2 saved).cells
  events := observations.physicalEvents false
  savedAtCommit := (CPR_SourceBank.copied_data (cached initial) 2 saved).trans written_checkpoint.symm
  loadedAtEntry := by
    rw [events]
    change MultiproofConeCanonical.bytesOf (e2.buffers 2).val =
      byteLedger (CPR_SourceBank.afterCopy (cached initial) 2 saved).cells 2
    rw [reader_checkpoint,CPR_SourceBank.copied_data]
  noInterveningWrite := by
    intro event member
    rw [events] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same <;> subst event <;> trivial

#print axioms events
#print axioms version
end AspisR1.SCE_FixtureVersion
end
