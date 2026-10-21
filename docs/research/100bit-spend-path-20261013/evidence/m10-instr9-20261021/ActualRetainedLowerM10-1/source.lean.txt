import ActualAllocationExtractorM10

/-! The complete allocator includes the previously counted retained caches.
Its positivity is not supplied solely by its final option/result group. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ActualRetainedLowerM10
open BinMerkle32Path
attribute [local irreducible] PublicRecoveryAllocationM10.typedCells PublicRecoveryAllocationM10.wordsCells

theorem batch_lower {n : Nat} (heap : Fin n → Nat) :
    3*n+1 ≤ AllocationBatchM10.cells heap := by
  unfold AllocationBatchM10.cells
  omega

theorem typed_lower (a b f : List BinEagerWordsReads.Leaf) :
    2949126 ≤ PublicRecoveryAllocationM10.typedCells a b f := by
  have ha := batch_lower (TypedCacheAllocationM10.c1Demand a)
  unfold PublicRecoveryAllocationM10.typedCells
  omega

theorem words_lower (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) :
    2949126 ≤ PublicRecoveryAllocationM10.wordsCells log f0 f2 f30 := by
  let a := BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)
  let b := BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)
  let f := BinEagerRecoveryWork.materialize (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)
  have ht := typed_lower a.1 b.1 f.1
  unfold PublicRecoveryAllocationM10.wordsCells
  change 2949126 ≤ _+_+_+PublicRecoveryAllocationM10.typedCells a.1 b.1 f.1+16
  omega

theorem stage_lower (run : RawCutProverCompiler.RunView) :
    2949126 ≤ PublicRecoveryAllocationM10.stageCells run := by
  have hw := words_lower run.1 (BinFrameReplayTotalWork.frameWork run 0).1
    (BinFrameReplayTotalWork.frameWork run 2).1 (BinFrameReplayTotalWork.frameWork run 30).1
  unfold PublicRecoveryAllocationM10.stageCells
  omega

theorem bound (run : RawRecordedEagerExtractorReadsBin.RunView)
    (coins : RawRecordedEagerExtractorReadsBin.Coins) :
    3019905024 ≤ ActualAllocationExtractorM10.actualHeap.bits run coins := by
  rw [ActualAllocationExtractorM10.counted_allocations]
  have hs := stage_lower run
  change 1024*2949126 ≤ 1024*_
  exact Nat.mul_le_mul_left 1024 (by omega)

#print axioms batch_lower
#print axioms typed_lower
#print axioms words_lower
#print axioms stage_lower
#print axioms bound
end AspisR1.ActualRetainedLowerM10
end
