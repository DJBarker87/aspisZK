import PublicPrimitiveDecoderWork
import BinEagerRecoveryWork

/-! Root/address preparation for each eager binary recovery demand. Counts
full length scans, suffix traversal, fixed 32-byte state reconstruction and
binary path geometry; all inputs to stateOfBytes are consumed at fixed width.
The path indices in the stage are fixed-width Fin 262144/Fin 65536 values. -/
set_option autoImplicit false
namespace AspisR1.BinRecoveryAddressWork
open BinMerkle32Path
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
abbrev Byte := BinMerkle32Path.Byte

def trailing (xs : Bytes) : Option State × Nat :=
  let n := PublicPrimitiveDecoderWork.length xs
  if 32 ≤ n.1 then
    let tail := BinLeafListWork.drop (n.1-32) xs
    (some (FS2.Duplex.stateOfBytes tail.1), n.2+tail.2+1024)
  else (none, n.2+2)

theorem trailing_value (xs : Bytes) : (trailing xs).1 = RawByteCollisionTargets.trailing xs := by
  simp only [trailing, PublicPrimitiveDecoderWork.length_value, BinLeafListWork.drop_value,
    RawByteCollisionTargets.trailing]
  split <;> rfl

theorem trailing_work (xs : Bytes) : (trailing xs).2 ≤ 2*xs.length+2048 := by
  have hn := PublicPrimitiveDecoderWork.length_work xs
  have hd := BinLeafListWork.drop_work ((PublicPrimitiveDecoderWork.length xs).1-32) xs
  have hv := PublicPrimitiveDecoderWork.length_value xs
  simp only [trailing]
  split <;> dsimp only <;> omega

def middle (xs : Bytes) : Option State × Nat :=
  let n := PublicPrimitiveDecoderWork.length xs
  if 70 ≤ n.1 then
    let tail := BinLeafListWork.drop 38 xs
    (some (FS2.Duplex.stateOfBytes tail.1), n.2+tail.2+1024)
  else (none, n.2+2)

theorem middle_value (xs : Bytes) : (middle xs).1 = RawByteCollisionTargets.fixed 38 xs := by
  simp only [middle, PublicPrimitiveDecoderWork.length_value, BinLeafListWork.drop_value,
    RawByteCollisionTargets.fixed]
  split <;> rfl

theorem middle_work (xs : Bytes) : (middle xs).2 ≤ 2*xs.length+2048 := by
  have hn := PublicPrimitiveDecoderWork.length_work xs
  have hd := BinLeafListWork.drop_work 38 xs
  simp only [middle]
  split <;> dsimp only <;> omega

def root (mid : Bool) (xs : Bytes) : State × Nat :=
  let r := if mid then middle xs else trailing xs
  (r.1.getD default, r.2+2)

theorem root_value (mid : Bool) (xs : Bytes) : (root mid xs).1 =
    RawCutWordsFromView.rootFrom (if mid then 9 else 8) xs := by
  cases mid <;>
    simp only [root, Bool.false_eq_true, if_false, if_true, middle_value, trailing_value,
      RawCutWordsFromView.rootFrom, RawByteCollisionTargets.pred_middle,
      RawByteCollisionTargets.pred_tail]

theorem root_work (mid : Bool) (xs : Bytes) : (root mid xs).2 ≤ 2*xs.length+2050 := by
  have ht := trailing_work xs
  have hm := middle_work xs
  cases mid <;> simp only [root, Bool.false_eq_true, if_false, if_true] <;> omega

def slots : Nat → Nat → List (Fin 2) × Nat
  | 0, _ => ([], 1)
  | d+1, i => let r := slots d (i/2); (BinMultiproof.slot i::r.1, r.2+8)

theorem slots_value (d i : Nat) : (slots d i).1 = BinMultiproof.slots d i := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp only [slots, BinMultiproof.slots, ih]

theorem slots_work (d i : Nat) : (slots d i).2 = 8*d+1 := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp only [slots, ih]; omega

def leaf (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (mid : Bool) (i : Nat) : BinEagerWordsReads.Leaf × Nat :=
  let r := root mid frame
  let s := slots 18 i
  let t := BinCutRecoveryWork.recover tag width frame log s.1 r.1
  (t.1.map Prod.fst, t.2+r.2+s.2+4)

theorem leaf_value (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (mid : Bool) (i : Nat) : (leaf tag width log frame mid i).1 =
    (BinEagerRecoveryWork.leaf tag width log frame
      (RawCutWordsFromView.rootFrom (if mid then 9 else 8) frame) i).1 := by
  simp only [leaf, slots_value, root_value, BinEagerRecoveryWork.leaf,
    BinCutRecoveryWork.recover_value, BinEagerWordsReads.leafRead,
    BinRecordedRecoveryReads.cutRecover_value]

theorem leaf_work (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (mid : Bool) (i : Nat)
    (hw : width ≤ 480) (hf : frame.length ≤ 131072) :
    (leaf tag width log frame mid i).2 ≤ 273355*log.length+300000 := by
  have hr := root_work mid frame
  have hs := slots_work 18 i
  have ht := BinCutRecoveryWork.recover_work tag width frame log
    (slots 18 i).1 (root mid frame).1 hw (by
      rw [slots_value, BinMultiproof.slots_length])
  have hm := Nat.mul_le_mul_right log.length
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hf) 11211)
  change _+_+_+4 ≤ _
  omega

#print axioms trailing_value
#print axioms trailing_work
#print axioms middle_value
#print axioms middle_work
#print axioms root_value
#print axioms root_work
#print axioms slots_value
#print axioms slots_work
#print axioms leaf_value
#print axioms leaf_work
end AspisR1.BinRecoveryAddressWork
