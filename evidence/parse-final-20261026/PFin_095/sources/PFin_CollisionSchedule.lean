import AuS1_Finish
import PFin_CollisionInsertion
import PFin_CheckpointSeparation
import PFin_ReplaySplit
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CollisionSchedule
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem transport (H : Bytes → State) (before prep source : List (Bytes × State))
    (physical : F3_Model.PhysicalPublic) (stored : Bytes) (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs) (v : LiteralOpeningView.View)
    (physicalLong : 514<physical.bytes.length) (storedLong : 514<stored.length)
    (first : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true)
    (schedule : source=prep ++ ((eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
      ((eval H (F3_Model.checkpoint physical stored p q tr i v)).1 ++
        (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1)))
    (beforeCons : ∀ x∈before,x.2=H x.1) (sourceCons : ∀ x∈source,x.2=H x.1)
    (r : Nat) (budget : firstReads emptyTable (before++source++(eval H (SdkC_Replay.replay p q)).1)≤r)
    (hit : AuS1_Finish.Collision H (before++prep) p q) :
    hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred r)
      emptyTable (before++source++(eval H (SdkC_Replay.replay p q)).1) := by
  let left := before++prep++(eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1
  have prepCons : ∀ x∈prep,x.2=H x.1 := by
    intro x member
    apply sourceCons x
    rw [schedule]
    exact List.mem_append_left _ member
  have oldCons : ∀ x∈left++(eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1,x.2=H x.1 := by
    intro x member
    simp only [left,List.mem_append] at member
    rcases member with ((old | prepared) | batch0) | batch1
    · exact beforeCons x old
    · exact prepCons x prepared
    · exact FS.eval_consistent H _ x batch0
    · exact FS.eval_consistent H _ x batch1
  have fullCons : ∀ x∈before++source++(eval H (SdkC_Replay.replay p q)).1,x.2=H x.1 := by
    intro x member
    rcases List.mem_append.mp member with old | replay
    · rcases List.mem_append.mp old with earlier | sourceRead
      · exact beforeCons x earlier
      · exact sourceCons x sourceRead
    · exact FS.eval_consistent H _ x replay
  have disjoint := PFin_CheckpointSeparation.disjoint H physical stored p q tr i v physicalLong storedLong OraclePortFrozen2.batch1
  have oldHit : hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred
      (firstReads emptyTable (before++prep)+1040)) emptyTable
      (left++(eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1) := by
    simpa only [AuS1_Finish.Collision,PFin_ReplaySplit.log H p q first,left,List.append_assoc] using hit
  have enlarged := PFin_CollisionInsertion.transport SelectedTranscriptParams.params.iv BinRawByteCollisionTargets.pred H
    left (eval H (F3_Model.checkpoint physical stored p q tr i v)).1
    (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1 (eval H (SdkC_Replay.replay p q)).1
    _ r oldCons
    (by simpa only [left,schedule,List.append_assoc] using fullCons) disjoint
    (by simpa only [left,schedule,List.append_assoc] using budget) oldHit
  simpa only [left,schedule,List.append_assoc] using enlarged

#print axioms transport
end AspisR1.PFin_CollisionSchedule
end
