import PublicCursorAllocationM10
import BinTypedWordDemandWork

set_option autoImplicit false
namespace AspisR1.TypedCacheAllocationM10
open PublicCursorAllocationM10 ListConstructorAllocationM10
abbrev Byte := BinMerkle32Path.Byte
abbrev Leaf := BinEagerWordsReads.Leaf

def lookupCells {A : Type} : List A → Nat → Nat
  | [], _ => 1
  | _::_, 0 => 1
  | _::xs, i+1 => lookupCells xs i+1

theorem lookup_work {A : Type} (xs : List A) (i : Nat) :
    lookupCells xs i ≤ (BinTypedCacheWork.lookup xs i).2 := by
  induction xs generalizing i with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i => exact Nat.add_le_add_right (ih i) 1

def qm31Cells (xs : List Byte) : Nat := xs.length+1+256
def wideCells (xs : List Byte) : Nat := xs.length+1+512

theorem qm31_work (xs : List Byte) : qm31Cells xs ≤ (BinTypedCacheWork.qm31 xs).2 := by
  simp only [qm31Cells,BinTypedCacheWork.qm31,PublicPrimitiveDecoderWork.length_work]
  omega

theorem wide_work (xs : List Byte) : wideCells xs ≤ (BinTypedCacheWork.wide xs).2 := by
  simp only [wideCells,BinTypedCacheWork.wide,PublicPrimitiveDecoderWork.length_work]
  omega

def c1slotCells (xs : List Byte) : Nat :=
  takeCells 104 xs+dropCells 104 xs+
    decodeCells PublicPrimitiveDecoderWork.field fieldCells 4 26 (BinLeafListWork.take 104 xs).1+
    qm31Cells (BinLeafListWork.drop 104 xs).1+4

theorem c1slot_work (xs : List Byte) : c1slotCells xs ≤ (BinTypedCacheWork.c1slot xs).2 := by
  have hp := take_work 104 xs
  have hs := drop_work 104 xs
  have hw := decode_work _ _ field_work 4 26 (BinLeafListWork.take 104 xs).1
  have ht := qm31_work (BinLeafListWork.drop 104 xs).1
  change _+_+_+_+4 ≤ _+_+_+_+5
  omega

def c2slotCells := decodeCells BinTypedCacheWork.qm31 qm31Cells 16 2

theorem c2slot_work (xs : List Byte) : c2slotCells xs ≤ (BinTypedCacheWork.c2slot xs).2 :=
  decode_work _ _ qm31_work 16 2 xs

def c1Cells := decodeCells BinTypedCacheWork.c1slot c1slotCells 120 4
def c2Cells := decodeCells BinTypedCacheWork.c2slot c2slotCells 32 4
def foldedCells := decodeCells BinTypedCacheWork.wide wideCells 32 4

theorem c1_work (xs : List Byte) : c1Cells xs ≤ (BinTypedCacheWork.c1 xs).2 :=
  decode_work _ _ c1slot_work 120 4 xs

theorem c2_work (xs : List Byte) : c2Cells xs ≤ (BinTypedCacheWork.c2 xs).2 :=
  decode_work _ _ c2slot_work 32 4 xs

theorem folded_work (xs : List Byte) : foldedCells xs ≤ (BinTypedCacheWork.folded xs).2 :=
  decode_work _ _ wide_work 32 4 xs

def demandCells {n : Nat} (heap : List Byte → Nat) (xs : List Leaf) (i : Fin n) : Nat :=
  lookupCells xs i.val+1+
    (match (BinTypedCacheWork.cached xs i).1 with | none => 0 | some bs => heap bs)+2

theorem demand_work {A : Type} {n : Nat} (d : List Byte → Option A × Nat)
    (heap : List Byte → Nat) (h : ∀ xs, heap xs ≤ (d xs).2)
    (xs : List Leaf) (i : Fin n) :
    demandCells heap xs i ≤ (BinTypedCacheWork.demand d xs i).2 := by
  have hl := lookup_work xs i.val
  cases ho : (BinTypedCacheWork.cached xs i).1 with
  | none =>
    simp only [demandCells,BinTypedCacheWork.demand,ho]
    change _ ≤ (BinTypedCacheWork.lookup xs i.val).2+2+64
    omega
  | some bs =>
    have hd := h bs
    simp only [demandCells,BinTypedCacheWork.demand,ho]
    change _ ≤ (BinTypedCacheWork.lookup xs i.val).2+2+(d bs).2+64
    omega

def c1Demand (xs : List Leaf) (i : Fin 1048576) := demandCells c1Cells xs (TypedRecoveredWords.queryLeaf i)
def c2Demand (xs : List Leaf) (i : Fin 1048576) := demandCells c2Cells xs (TypedRecoveredWords.queryLeaf i)
def finalDemand (xs : List Leaf) (i : Fin 262144) := demandCells foldedCells xs (MerkleIndexGeometry.foldedIndex i)

theorem c1_demand_work (xs : List Leaf) (i : Fin 1048576) :
    c1Demand xs i ≤ (BinTypedWordDemandWork.c1 xs i).2 := demand_work _ _ c1_work _ _
theorem c2_demand_work (xs : List Leaf) (i : Fin 1048576) :
    c2Demand xs i ≤ (BinTypedWordDemandWork.c2 xs i).2 := demand_work _ _ c2_work _ _
theorem final_demand_work (xs : List Leaf) (i : Fin 262144) :
    finalDemand xs i ≤ (BinTypedWordDemandWork.finalWord xs i).2 := demand_work _ _ folded_work _ _

#print axioms lookup_work
#print axioms qm31_work
#print axioms wide_work
#print axioms c1slot_work
#print axioms c2slot_work
#print axioms c1_work
#print axioms c2_work
#print axioms folded_work
#print axioms demand_work
#print axioms c1_demand_work
#print axioms c2_demand_work
#print axioms final_demand_work
end AspisR1.TypedCacheAllocationM10
