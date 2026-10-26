import RecoveryParserAllocationM10
import BinRecoveryAddressWork

set_option autoImplicit false
namespace AspisR1.RecoveryWalkAllocationM10
open BinMerkle32Path BinMerkleTable
open BinMerkleLeafRecovery (Leaves)
open ListConstructorAllocationM10 RecoveryParserAllocationM10

def digestCells (a b : Digest) : Nat := equalCells (List.ofFn a) (List.ofFn b)+66

theorem digest_work (a b : Digest) : digestCells a b ≤ (BinRecoveryWork.digestEq a b).2 :=
  Nat.add_le_add_right (equal_work _ _) 66

def lookupCells {A : Type} : List (A × Digest) → Digest → Nat
  | [], _ => 1
  | (_,h)::rest, d =>
    if (BinRecoveryWork.digestEq h d).1 then digestCells h d+2
    else digestCells h d+lookupCells rest d+2

theorem lookup_work {A : Type} (xs : List (A × Digest)) (d : Digest) :
    lookupCells xs d ≤ (BinRecoveryWork.lookup xs d).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons p xs ih =>
    rcases p with ⟨a,h⟩
    have he := digest_work h d
    simp only [lookupCells,BinRecoveryWork.lookup]
    split <;> omega

def walkCells (nodes : Nodes) : List (Fin 2) → Digest → Nat
  | [], _ => 1
  | _::slots, root =>
    match (BinRecoveryWork.walk nodes slots root).1 with
    | none => walkCells nodes slots root+2
    | some parent => walkCells nodes slots root+lookupCells nodes parent+2

theorem walk_work (nodes : Nodes) (slots : List (Fin 2)) (root : Digest) :
    walkCells nodes slots root ≤ (BinRecoveryWork.walk nodes slots root).2 := by
  induction slots with
  | nil => exact Nat.le_refl _
  | cons slot slots ih =>
    cases h : (BinRecoveryWork.walk nodes slots root).1 with
    | none => simp only [walkCells,BinRecoveryWork.walk,h]; omega
    | some parent =>
      have hl := lookup_work nodes parent
      simp only [walkCells,BinRecoveryWork.walk,h]
      omega

def recoverCells (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2)) (root : Digest) : Nat :=
  walkCells nodes slots root+
    (match (BinRecoveryWork.walk nodes slots root).1 with
    | none => 0
    | some d => lookupCells leaves d)+2

theorem recover_work (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2)) (root : Digest) :
    recoverCells nodes leaves slots root ≤ (BinRecoveryWork.recover nodes leaves slots root).2 := by
  have hw := walk_work nodes slots root
  cases h : (BinRecoveryWork.walk nodes slots root).1 with
  | none => simp only [recoverCells,BinRecoveryWork.recover,h]; omega
  | some d =>
    have hl := lookup_work leaves d
    simp only [recoverCells,BinRecoveryWork.recover,h]
    omega

def firstCells (frame : List Byte) : BinMerkleRecordedLog.Log → Nat
  | [] => 1
  | (input,_)::rest =>
    if (BinLeafListWork.equal frame input).1 then equalCells frame input+2
    else equalCells frame input+firstCells frame rest+2

theorem first_work (frame : List Byte) (log : BinMerkleRecordedLog.Log) :
    firstCells frame log ≤ (BinCutRecoveryWork.firstIndex frame log).2 := by
  induction log with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    rcases p with ⟨input,digest⟩
    have he := equal_work frame input
    simp only [firstCells,BinCutRecoveryWork.firstIndex]
    split <;> omega

def cutCells (frame : List Byte) (log : BinMerkleRecordedLog.Log) : Nat :=
  firstCells frame log+takeCells (BinCutRecoveryWork.firstIndex frame log).1 log+2

theorem cut_work (frame : List Byte) (log : BinMerkleRecordedLog.Log) :
    cutCells frame log ≤ (BinCutRecoveryWork.cut frame log).2 := by
  have hf := first_work frame log
  have ht := take_work (BinCutRecoveryWork.firstIndex frame log).1 log
  change _+_+2 ≤ _+_+4
  omega

def cutRecoverCells (tag : Byte) (width : Nat) (frame : List Byte)
    (log : BinMerkleRecordedLog.Log) (slots : List (Fin 2)) (root : Digest) : Nat :=
  let c := BinCutRecoveryWork.cut frame log
  let t := BinTableWork.tables tag width c.1
  cutCells frame log+tableCells tag width c.1+recoverCells t.1.1 t.1.2 slots root+4

theorem cut_recover_work (tag : Byte) (width : Nat) (frame : List Byte)
    (log : BinMerkleRecordedLog.Log) (slots : List (Fin 2)) (root : Digest) :
    cutRecoverCells tag width frame log slots root ≤
      (BinCutRecoveryWork.recover tag width frame log slots root).2 := by
  have hc := cut_work frame log
  have ht := table_work tag width (BinCutRecoveryWork.cut frame log).1
  have hr := recover_work
    (BinTableWork.tables tag width (BinCutRecoveryWork.cut frame log).1).1.1
    (BinTableWork.tables tag width (BinCutRecoveryWork.cut frame log).1).1.2 slots root
  change _+_+_+4 ≤ _+_+_+8
  omega

/-- Fixed 32-byte state reconstruction; drop only borrows the suffix. -/
def trailingCells (xs : List Byte) : Nat :=
  if 32 ≤ (PublicPrimitiveDecoderWork.length xs).1 then
    xs.length+1+dropCells ((PublicPrimitiveDecoderWork.length xs).1-32) xs+33
  else xs.length+1+1

def middleCells (xs : List Byte) : Nat :=
  if 70 ≤ (PublicPrimitiveDecoderWork.length xs).1 then xs.length+1+dropCells 38 xs+33
  else xs.length+1+1

theorem trailing_work (xs : List Byte) : trailingCells xs ≤ (BinRecoveryAddressWork.trailing xs).2 := by
  have hd := drop_work ((PublicPrimitiveDecoderWork.length xs).1-32) xs
  simp only [trailingCells,BinRecoveryAddressWork.trailing,PublicPrimitiveDecoderWork.length_work]
  split <;> omega

theorem middle_work (xs : List Byte) : middleCells xs ≤ (BinRecoveryAddressWork.middle xs).2 := by
  have hd := drop_work 38 xs
  simp only [middleCells,BinRecoveryAddressWork.middle,PublicPrimitiveDecoderWork.length_work]
  split <;> omega

def rootCells (mid : Bool) (xs : List Byte) : Nat :=
  (if mid then middleCells xs else trailingCells xs)+1

theorem root_work (mid : Bool) (xs : List Byte) : rootCells mid xs ≤ (BinRecoveryAddressWork.root mid xs).2 := by
  have ht := trailing_work xs
  have hm := middle_work xs
  cases mid <;> simp only [rootCells,BinRecoveryAddressWork.root,Bool.false_eq_true,if_false,if_true] <;> omega

def slotsCells : Nat → Nat
  | 0 => 1
  | d+1 => slotsCells d+2

theorem slots_work (d i : Nat) : slotsCells d ≤ (BinRecoveryAddressWork.slots d i).2 := by
  induction d generalizing i with
  | zero => exact Nat.le_refl _
  | succ d ih => exact (Nat.add_le_add_right (ih (i/2)) 2).trans (by change _+2 ≤ _+8; omega)

def leafCells (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (mid : Bool) (i : Nat) : Nat :=
  cutRecoverCells tag width frame log (BinRecoveryAddressWork.slots 18 i).1
    (BinRecoveryAddressWork.root mid frame).1+rootCells mid frame+slotsCells 18+2

theorem leaf_work (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (mid : Bool) (i : Nat) :
    leafCells tag width log frame mid i ≤ (BinRecoveryAddressWork.leaf tag width log frame mid i).2 := by
  have hc := cut_recover_work tag width frame log (BinRecoveryAddressWork.slots 18 i).1
    (BinRecoveryAddressWork.root mid frame).1
  have hr := root_work mid frame
  have hs := slots_work 18 i
  change _+_+_+2 ≤ _+_+_+4
  omega

#print axioms digest_work
#print axioms lookup_work
#print axioms walk_work
#print axioms recover_work
#print axioms first_work
#print axioms cut_work
#print axioms cut_recover_work
#print axioms trailing_work
#print axioms middle_work
#print axioms root_work
#print axioms slots_work
#print axioms leaf_work
end AspisR1.RecoveryWalkAllocationM10
