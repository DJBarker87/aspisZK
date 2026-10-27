import FrameReplayAllocationM10
import RecoveryWalkAllocationM10
import TypedCacheAllocationM10
import AllocationBatchM10
import BinPublicRecoverySharedStageM10

set_option autoImplicit false
namespace AspisR1.PublicRecoveryAllocationM10
open BinMerkle32Path

def typedCells (a b f : List BinEagerWordsReads.Leaf) : Nat :=
  AllocationBatchM10.cells (TypedCacheAllocationM10.c1Demand a)+
  AllocationBatchM10.cells (TypedCacheAllocationM10.c2Demand b)+
  AllocationBatchM10.cells (TypedCacheAllocationM10.finalDemand f)+16

theorem typed_work (a b f : List BinEagerWordsReads.Leaf) :
    typedCells a b f ≤ (BinPublicRecoverySharedStageM10.typedWords a b f).2 := by
  have ha := AllocationBatchM10.batch_work (BinTypedWordDemandWork.c1 a) _
    (TypedCacheAllocationM10.c1_demand_work a)
  have hb := AllocationBatchM10.batch_work (BinTypedWordDemandWork.c2 b) _
    (TypedCacheAllocationM10.c2_demand_work b)
  have hf := AllocationBatchM10.batch_work (BinTypedWordDemandWork.finalWord f) _
    (TypedCacheAllocationM10.final_demand_work f)
  change _+_+_+16 ≤ _+_+_+16
  omega

def wordsCells (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) : Nat :=
  let t1 := BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)
  let t2 := BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)
  let tf := BinEagerRecoveryWork.materialize (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)
  AllocationBatchM10.cells (fun i : Fin 262144 => RecoveryWalkAllocationM10.leafCells 0x71 480 log f0 false i.val)+
  AllocationBatchM10.cells (fun i : Fin 262144 => RecoveryWalkAllocationM10.leafCells 0xf1 128 log f2 false i.val)+
  AllocationBatchM10.cells (fun i : Fin 65536 => RecoveryWalkAllocationM10.leafCells 0x72 128 log f30 true i.val)+
  typedCells t1.1 t2.1 tf.1+16

theorem words_work (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) :
    wordsCells log f0 f2 f30 ≤ (BinPublicRecoverySharedStageM10.words log f0 f2 f30).2 := by
  have ha := AllocationBatchM10.recovery_work
    (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val) _
    (fun i => RecoveryWalkAllocationM10.leaf_work _ _ _ _ _ _)
  have hb := AllocationBatchM10.recovery_work
    (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val) _
    (fun i => RecoveryWalkAllocationM10.leaf_work _ _ _ _ _ _)
  have hf := AllocationBatchM10.recovery_work
    (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val) _
    (fun i => RecoveryWalkAllocationM10.leaf_work _ _ _ _ _ _)
  have ht := typed_work
    (BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)).1
    (BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)).1
    (BinEagerRecoveryWork.materialize (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)).1
  change _+_+_+_+16 ≤ _+_+_+_+16
  omega

def stageCells (run : RawCutProverCompiler.RunView) : Nat :=
  (FrameReplayAllocationM10.frame run 0).cells+(FrameReplayAllocationM10.frame run 2).cells+
  (FrameReplayAllocationM10.frame run 30).cells+
  wordsCells run.1 (BinFrameReplayTotalWork.frameWork run 0).1
    (BinFrameReplayTotalWork.frameWork run 2).1 (BinFrameReplayTotalWork.frameWork run 30).1

theorem stage_work (run : RawCutProverCompiler.RunView) :
    stageCells run ≤ (BinPublicRecoverySharedStageM10.stage run).2 := by
  have ha := FrameReplayAllocationM10.frame_cells_work run 0
  have hb := FrameReplayAllocationM10.frame_cells_work run 2
  have hf := FrameReplayAllocationM10.frame_cells_work run 30
  have hw := words_work run.1 (BinFrameReplayTotalWork.frameWork run 0).1
    (BinFrameReplayTotalWork.frameWork run 2).1 (BinFrameReplayTotalWork.frameWork run 30).1
  change _+_+_+_ ≤ _+_+_+_
  omega

@[irreducible] def spec (Q : Nat) : AllocationStageSpecM10.StageSpec 1024
    (fun run : RawCutProverCompiler.RunView => some (BinEagerWordsReads.words run).1)
    (fun run => run.1.length ≤ Q) (fun _ => True) (fun _ => 4000000000000*(Q+1)) where
  run run := (some (BinPublicRecoverySharedStageM10.stage run).1,(BinPublicRecoverySharedStageM10.stage run).2)
  value run := congrArg some (BinPublicRecoverySharedStageM10.stage_value run)
  work _ run h := (BinPublicRecoverySharedStageM10.stage_work run).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
  invariant _ _ _ _ := True.intro
  allocation run := ⟨stageCells run,1024*stageCells run,Nat.le_refl _,stage_work run⟩

#print axioms typed_work
#print axioms words_work
#print axioms stage_work
end AspisR1.PublicRecoveryAllocationM10
