import BinTypedCacheWork

set_option autoImplicit false
namespace AspisR1.BinTypedWordDemandWork
open BinTypedCacheWork
abbrev Byte := PublicPrimitiveDecoderWork.Byte
abbrev Leaf := BinEagerWordsReads.Leaf

def c1 (table : List Leaf) (i : Fin 1048576) : MixedLeafEncoding.C1Slot × Nat :=
  let r := demand BinTypedCacheWork.c1 table (TypedRecoveredWords.queryLeaf i)
  ((r.1.getD TypedRecoveredWords.zeroC1) (TypedRecoveredWords.querySlot i), r.2)
def c2 (table : List Leaf) (i : Fin 1048576) : MixedLeafEncoding.C2Slot × Nat :=
  let r := demand BinTypedCacheWork.c2 table (TypedRecoveredWords.queryLeaf i)
  ((r.1.getD TypedRecoveredWords.zeroC2) (TypedRecoveredWords.querySlot i), r.2)
def finalWord (table : List Leaf) (i : Fin 262144) : FoldedLeafCodec.Wide × Nat :=
  let r := demand BinTypedCacheWork.folded table (MerkleIndexGeometry.foldedIndex i)
  ((r.1.getD FoldedRecoveredWord.zeroFolded) (FoldedRecoveredWord.foldedSlot i), r.2)

theorem c1_value (table : List Leaf) (i : Fin 1048576) :
    (c1 table i).1 = TypedRecoveredWords.c1Value (BinEagerWordsReads.cached table) i := by
  simp only [c1, demand_value, BinTypedCacheWork.c1_value,
    TypedRecoveredWords.c1Value, TypedRecoveredWords.decodeC1At]
theorem c2_value (table : List Leaf) (i : Fin 1048576) :
    (c2 table i).1 = TypedRecoveredWords.c2Value (BinEagerWordsReads.cached table) i := by
  simp only [c2, demand_value, BinTypedCacheWork.c2_value,
    TypedRecoveredWords.c2Value, TypedRecoveredWords.decodeC2At]
theorem finalWord_value (table : List Leaf) (i : Fin 262144) :
    (finalWord table i).1 = FoldedRecoveredWord.wordOfPacked
      (BinEagerWordsReads.cached table (MerkleIndexGeometry.foldedIndex i)) i := by
  simp only [finalWord, demand_value, BinTypedCacheWork.folded_value,
    FoldedRecoveredWord.wordOfPacked]

theorem c1_work (table : List Leaf) (i : Fin 1048576) : (c1 table i).2 ≤ 311671 :=
  demand_work BinTypedCacheWork.c1 49461 BinTypedCacheWork.c1_work table _
theorem c2_work (table : List Leaf) (i : Fin 1048576) : (c2 table i).2 ≤ 295947 :=
  demand_work BinTypedCacheWork.c2 33737 BinTypedCacheWork.c2_work table _
theorem finalWord_work (table : List Leaf) (i : Fin 262144) : (finalWord table i).2 ≤ 131675 :=
  demand_work BinTypedCacheWork.folded 66073 BinTypedCacheWork.folded_work table _

/-- Explicit finite batch. Array.ofFn materializes each demand once; the
parallel sum counts every invocation and the array slots and loop steps. -/
def materialize {A : Type} {n : Nat} (f : Fin n → A × Nat) : Array A × Nat :=
  (Array.ofFn (fun i => (f i).1), ((List.ofFn f).map Prod.snd).sum + 3*n+1)

theorem materialize_size {A : Type} {n : Nat} (f : Fin n → A × Nat) :
    (materialize f).1.size = n := Array.size_ofFn

def readMaterialized {A : Type} {n : Nat} (f : Fin n → A × Nat) (i : Fin n) : A :=
  (materialize f).1[i.val]'(by rw [materialize_size]; exact i.isLt)

theorem materialize_value {A : Type} {n : Nat} (f : Fin n → A × Nat) (i : Fin n) :
    readMaterialized f i = (f i).1 := by
  simp only [readMaterialized, materialize, Array.getElem_ofFn]

theorem materialize_work {A : Type} {n : Nat} (f : Fin n → A × Nat)
    (c : Nat) (hf : ∀ i, (f i).2 ≤ c) : (materialize f).2 ≤ n*(c+3)+1 := by
  have hs := BinEagerWordsReads.sum_bound ((List.ofFn f).map Prod.snd) c (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact hf i)
  simp only [List.length_map, List.length_ofFn] at hs
  change _+3*n+1 ≤ _
  nlinarith

def words (a b f : List Leaf) : CanonicalCutEnrichedTranscript.Words × Nat :=
  let ca := materialize (c1 a)
  let cb := materialize (c2 b)
  let cf := materialize (finalWord f)
  (⟨readMaterialized (c1 a), readMaterialized (c2 b), readMaterialized (finalWord f)⟩,
    ca.2+cb.2+cf.2+16)

attribute [local irreducible] readMaterialized c1 c2 finalWord

theorem words_value (a b f : List Leaf) : (words a b f).1 =
    CanonicalCutEnrichedTranscript.wordsFromMaps (BinEagerWordsReads.cached a)
      (BinEagerWordsReads.cached b) (BinEagerWordsReads.cached f) := by
  unfold words CanonicalCutEnrichedTranscript.wordsFromMaps
  dsimp only
  congr 1
  · funext i; exact (materialize_value (c1 a) i).trans (c1_value a i)
  · funext i; exact (materialize_value (c2 b) i).trans (c2_value b i)
  · funext i; exact (materialize_value (finalWord f) i).trans (finalWord_value f i)

theorem words_work (a b f : List Leaf) : (words a b f).2 ≤ 1000000000000 := by
  have ha := materialize_work (c1 a) 311671 (c1_work a)
  have hb := materialize_work (c2 b) 295947 (c2_work b)
  have hf := materialize_work (finalWord f) 131675 (finalWord_work f)
  change _+_+_+16 ≤ _
  omega

#print axioms c1_value
#print axioms c2_value
#print axioms finalWord_value
#print axioms c1_work
#print axioms c2_work
#print axioms finalWord_work
#print axioms materialize_size
#print axioms materialize_value
#print axioms materialize_work
#print axioms words_value
#print axioms words_work
end AspisR1.BinTypedWordDemandWork
