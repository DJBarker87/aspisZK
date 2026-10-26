import BinRecoveryWork

/-! Cut copying and every repeated table/recovery demand, with explicit
byte-comparison work. Frame construction/replay is outside this component. -/
set_option autoImplicit false
namespace AspisR1.BinCutRecoveryWork
open BinMerkle32Path
open BinMerkleLeafRecovery (LeafData)
open BinMerkleRecordedLog (Log)

def firstIndex (frame : List Byte) : Log → Nat × Nat
  | [] => (0, 1)
  | (input, _) :: rest =>
    let eq := BinLeafListWork.equal frame input
    if eq.1 then (0, eq.2 + 4)
    else let r := firstIndex frame rest; (r.1 + 1, eq.2 + r.2 + 4)

theorem firstIndex_value (frame : List Byte) (log : Log) :
    (firstIndex frame log).1 = RawCutRecordedWordsExecutable.firstIndexExec frame log := by
  induction log with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨input, digest⟩
    by_cases h : frame = input
    · simp only [firstIndex, BinLeafListWork.equal_value, h,
        RawCutRecordedWordsExecutable.firstIndexExec, decide_true,
        Bool.true_eq, if_true]
    · have hh : input ≠ frame := Ne.symm h
      simp only [firstIndex, BinLeafListWork.equal_value, h, hh,
        RawCutRecordedWordsExecutable.firstIndexExec, decide_false,
        Bool.false_eq_true, if_false, ih]

theorem firstIndex_work (frame : List Byte) (log : Log) :
    (firstIndex frame log).2 ≤ log.length * (2 * frame.length + 5) + 1 := by
  induction log with
  | nil => simp only [firstIndex, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | cons p rest ih =>
    rcases p with ⟨input, digest⟩
    have he := BinLeafListWork.equal_work frame input
    simp only [firstIndex, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> omega

theorem firstIndex_le (frame : List Byte) (log : Log) :
    (firstIndex frame log).1 ≤ log.length := by
  induction log with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    rcases p with ⟨input, digest⟩
    simp only [firstIndex, List.length_cons]
    split <;> omega

def cut (frame : List Byte) (log : Log) : Log × Nat :=
  let i := firstIndex frame log
  let t := BinLeafListWork.take i.1 log
  (t.1, i.2 + t.2 + 4)

theorem cut_value (frame : List Byte) (log : Log) :
    (cut frame log).1 = RawCutRecordedWordsBoundedBin.cutBeforeExec log frame := by
  simp only [cut, BinLeafListWork.take_value, firstIndex_value,
    RawCutRecordedWordsBoundedBin.cutBeforeExec, RawCutRecordedWordsExecutable.cutBeforeExec]

theorem cut_length (frame : List Byte) (log : Log) : (cut frame log).1.length ≤ log.length := by
  simp only [cut, BinLeafListWork.take_value, List.length_take]
  exact Nat.min_le_right _ _

theorem cut_work (frame : List Byte) (log : Log) :
    (cut frame log).2 ≤ log.length * (2 * frame.length + 7) + 6 := by
  have hi := firstIndex_work frame log
  have ht := BinLeafListWork.take_work (firstIndex frame log).1 log
  have hl := firstIndex_le frame log
  change _ + _ + 4 ≤ _
  nlinarith

def recover (tag : Byte) (width : Nat) (frame : List Byte) (log : Log)
    (slots : List (Fin 2)) (root : Digest) : Option LeafData × Nat :=
  let c := cut frame log
  let t := BinTableWork.tables tag width c.1
  let r := BinRecoveryWork.recover t.1.1 t.1.2 slots root
  (r.1, c.2 + t.2 + r.2 + 8)

theorem recover_value (tag : Byte) (width : Nat) (frame : List Byte) (log : Log)
    (slots : List (Fin 2)) (root : Digest) : (recover tag width frame log slots root).1 =
      RawCutRecordedWordsBoundedBin.recoverAtExec tag width
        (RawCutRecordedWordsBoundedBin.cutBeforeExec log frame) slots root := by
  simp only [recover, BinRecoveryWork.recover_value, BinTableWork.tables_value,
    BinRecordedRecoveryReads.tables_value, cut_value,
    RawCutRecordedWordsBoundedBin.recoverAtExec, BinLeafBoundedTable.leaves_value]

theorem recover_work (tag : Byte) (width : Nat) (frame : List Byte) (log : Log)
    (slots : List (Fin 2)) (root : Digest) (hw : width ≤ 480)
    (hd : slots.length ≤ 18) : (recover tag width frame log slots root).2 ≤
      (2 * frame.length + 11211) * log.length + 111 := by
  have hc := cut_work frame log
  have hlen := cut_length frame log
  let t := BinTableWork.tables tag width (cut frame log).1
  have ht : t.2 ≤ 8544 * log.length + 1 :=
    (BinTableWork.fixed_width_work tag width _ hw).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 8544 hlen) 1)
  have hs : t.1.1.length ≤ log.length ∧ t.1.2.length ≤ log.length := by
    dsimp only [t]
    rw [BinTableWork.tables_value]
    obtain ⟨hn, hl⟩ := BinRecordedRecoveryReads.tables_sizes tag width (cut frame log).1
    exact ⟨hn.trans hlen, hl.trans hlen⟩
  have hr := BinRecoveryWork.recover_work t.1.1 t.1.2 slots root
  have hr' : (BinRecoveryWork.recover t.1.1 t.1.2 slots root).2 ≤
      18 * (140 * log.length + 5) + 140 * log.length + 6 :=
    hr.trans (Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul hd
        (Nat.add_le_add_right (Nat.mul_le_mul_left 140 hs.1) 5))
        (Nat.mul_le_mul_left 140 hs.2)) 6)
  change (cut frame log).2 + t.2 + _ + 8 ≤ _
  nlinarith

#print axioms firstIndex_value
#print axioms firstIndex_work
#print axioms firstIndex_le
#print axioms cut_value
#print axioms cut_length
#print axioms cut_work
#print axioms recover_value
#print axioms recover_work
end AspisR1.BinCutRecoveryWork
