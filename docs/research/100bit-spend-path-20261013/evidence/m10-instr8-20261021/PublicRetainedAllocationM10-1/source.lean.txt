import MaterializationAllocationM10
import BinPublicRecoverySharedStageM10

/-! Always-executed retained public-side caches: the three recovered-leaf
lists, and the three typed cache arrays with their captured table closures.
Frame/recovery/decoding temporaries are not included in this subledger. -/
set_option autoImplicit false
namespace AspisR1.PublicRetainedAllocationM10
open AllocationStageSpecM10 MaterializationAllocationM10
open BinMerkle32Path

def width : Nat := 1024
/-- A list cell for each materialized leaf; the empty tail is shared. -/
def leafCells : Nat := 262144+262144+65536
/-- Each typed cache has its slots, one array header and one capture cell. -/
def typedCells : Nat := (1048576+2)+(1048576+2)+(262144+2)
def retainedCells : Nat := leafCells+typedCells

theorem leaf_lower {n : Nat} (f : Fin n → BinEagerRecoveryWork.Leaf × Nat) :
    n ≤ (BinEagerRecoveryWork.materialize f).2 := by
  change n ≤ _+3*n+1
  omega

theorem typed_lower (a b f : List BinEagerWordsReads.Leaf) :
    typedCells ≤ (BinPublicRecoverySharedStageM10.typedWords a b f).2 := by
  have ha := batch_lower (BinTypedWordDemandWork.c1 a) 0 (fun _ => Nat.zero_le _)
  have hb := batch_lower (BinTypedWordDemandWork.c2 b) 0 (fun _ => Nat.zero_le _)
  have hf := batch_lower (BinTypedWordDemandWork.finalWord f) 0 (fun _ => Nat.zero_le _)
  unfold BinPublicRecoverySharedStageM10.typedWords
  dsimp only
  unfold typedCells
  omega

attribute [local irreducible] BinPublicRecoverySharedStageM10.typedWords BinEagerRecoveryWork.materialize

theorem words_lower (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) :
    retainedCells ≤ (BinPublicRecoverySharedStageM10.words log f0 f2 f30).2 := by
  have ha := leaf_lower (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)
  have hb := leaf_lower (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)
  have hf := leaf_lower (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)
  have ht := typed_lower
    (BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)).1
    (BinEagerRecoveryWork.materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)).1
    (BinEagerRecoveryWork.materialize (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)).1
  unfold BinPublicRecoverySharedStageM10.words
  dsimp only
  unfold retainedCells leafCells
  omega

attribute [local irreducible] BinPublicRecoverySharedStageM10.words

theorem stage_lower (run : RawCutProverCompiler.RunView) :
    retainedCells ≤ (BinPublicRecoverySharedStageM10.stage run).2 := by
  have h := words_lower run.1 (BinFrameReplayTotalWork.frameWork run 0).1
    (BinFrameReplayTotalWork.frameWork run 2).1 (BinFrameReplayTotalWork.frameWork run 30).1
  unfold BinPublicRecoverySharedStageM10.stage
  dsimp only
  omega

@[irreducible] def spec (Q : Nat) : AllocationStageSpecM10.StageSpec width
    (fun run : RawCutProverCompiler.RunView => some (BinEagerWordsReads.words run).1)
    (fun run => run.1.length ≤ Q) (fun _ => True) (fun _ => 4000000000000*(Q+1)) where
  run run := (some (BinPublicRecoverySharedStageM10.stage run).1,
    (BinPublicRecoverySharedStageM10.stage run).2)
  value run := congrArg some (BinPublicRecoverySharedStageM10.stage_value run)
  work _ run h := (BinPublicRecoverySharedStageM10.stage_work run).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
  invariant _ _ _ _ := True.intro
  allocation run := ⟨retainedCells,width*retainedCells,Nat.le_refl _,stage_lower run⟩

theorem exact_count (Q : Nat) (run : RawCutProverCompiler.RunView) :
    ((spec Q).allocation run).elements = 2949126 ∧
    ((spec Q).allocation run).bits = 3019905024 := by
  unfold spec
  constructor <;> rfl

theorem positive (Q : Nat) (run : RawCutProverCompiler.RunView) :
    0 < ((spec Q).allocation run).bits := by
  rw [(exact_count Q run).2]
  omega

theorem work_dominates (Q : Nat) (run : RawCutProverCompiler.RunView) :
    ((spec Q).allocation run).bits ≤ width*((spec Q).run run).2 :=
  allocation_le_work (spec Q) run

#print axioms leaf_lower
#print axioms typed_lower
#print axioms words_lower
#print axioms stage_lower
#print axioms exact_count
#print axioms positive
#print axioms work_dominates
end AspisR1.PublicRetainedAllocationM10
