import NHS_CheckpointPacket
import NHW_Prepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_CheckpointPort
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes3Namespaces
/-- Native operational writer packet at the exact current-caller carrier. -/
def source {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NGC_KNE_Caller.WriterDomain (toPrepared (Tx1Q_Carriers.prepared p))
   (toAccumulator (Tx1Q_Carriers.accumulator a)))
 (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) := do
 let out ← CheckpointBytes5Effect.erase (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash
   (NGC_KNE_Writer.sourceProgram (toPrepared (Tx1Q_Carriers.prepared p))
      (toAccumulator (Tx1Q_Carriers.accumulator a)) domain proof pub)
 ok ⟨out.val,out.property⟩
/-- This is precisely the full-Result op16 equation needed at NHL's reached
checkpoint cut once the SAME query producer supplies this domain. -/
theorem slot {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NGC_KNE_Caller.WriterDomain (toPrepared (Tx1Q_Carriers.prepared p))
   (toAccumulator (Tx1Q_Carriers.accumulator a)))
 (proof pub : Slice U8) (hash : H) :
 source D p a domain proof pub hash=Tx1Q_Install.writer D p a proof pub hash := by
 unfold source Tx1Q_Install.writer Port3_CheckpointInstall.writer
 rw [NGC_KNE_Writer.cohort_program_eq]
#print axioms slot
end AspisR1.NHW_CheckpointPort
