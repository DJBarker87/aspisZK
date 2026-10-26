import CheckpointBytes5Join

import F3Q_SliceIdentity
import F3N_WriterReturned
import Tx2N_Install
import S2X_RuntimeRetention
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CheckpointStage
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes3Namespaces
open MultiproofConeCanonical

theorem erased {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (base : VTop_Stages.Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub proof2 pub2 checkpoint : Slice U8)
    (saved : alloc.vec.Vec U8) (p2 : verifier.Prepared) (a2 : verifier.Accumulator)
    (writer : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved)
    (reader : (Tx2N_Install.inner base reserved query).op18 D checkpoint proof2 pub2 .S2 hash=ok (.Ok (p2,a2)))
    (history : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf checkpoint.val))
    (proofSame : bytesOf proof2.val=bytesOf proof.val) (pubSame : bytesOf pub2.val=bytesOf pub.val) :
    erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub)=ok (.Ok (p2,a2)) := by
  have wrote := F3N_WriterReturned.erased D hash p a proof pub saved writer
  have resumed := Tx2N_Install.reader_success base reserved query D hash checkpoint proof2 pub2 .S2 p2 a2 reader
  have ck : checkpoint=alloc.vec.Vec.deref saved := F3Q_SliceIdentity.slice _ _ (S2X.checkpoint_persistence _ _ history)
  have proofEq := F3Q_SliceIdentity.slice _ _ proofSame
  have pubEq := F3Q_SliceIdentity.slice _ _ pubSame
  rw [ck,proofEq,pubEq] at resumed
  simp only [CheckpointBytes5Join.stage,erase_bind,wrote,bind_tc_ok,CheckpointBytes5Resume.source]
  exact resumed

theorem effects {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (reserved : Bool) (p2 : verifier.Prepared) (a2 : verifier.Accumulator)
    (success : erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub)=ok (.Ok (p2,a2))) :
    ∃ after,run (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub) []=ok (.Ok (p2,a2),after) :=
  Port3_CheckpointInstall.erase_success_run _ _ _ _ success []

#print axioms erased
#print axioms effects
end AspisR1.F3Q_CheckpointStage
end
