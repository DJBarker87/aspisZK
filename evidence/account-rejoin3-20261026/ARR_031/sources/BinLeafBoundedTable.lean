import BinLeafBoundedLength

/-! Compose the bounded length tests across every table-entry occurrence.
This counts neither distinct entries nor just successful leaf parses. -/
set_option autoImplicit false
namespace AspisR1.BinLeafBoundedTable
open BinMerkle32Path
open BinMerkleRecordedLog (Log)
open BinMerkleLeafRecovery (Leaves)

def leaves (tag : Byte) (width : Nat) (log : Log) : Leaves × Nat :=
  (log.filterMap (fun entry =>
    ((BinLeafBoundedLength.parse tag width entry.1).1).map fun data => (data, entry.2)),
   (log.map fun entry => (BinLeafBoundedLength.parse tag width entry.1).2).sum)

theorem leaves_value (tag : Byte) (width : Nat) (log : Log) :
    (leaves tag width log).1 = BinMerkleRecordedLog.leaves tag width log := by
  simp only [leaves, BinLeafBoundedLength.parse_value, BinMerkleRecordedLog.leaves]

theorem leaves_length_test_cost (tag : Byte) (width : Nat) (log : Log) :
    (leaves tag width log).2 ≤ log.length * (width + 34) := by
  induction log with
  | nil => simp [leaves]
  | cons entry rest ih =>
    have hp := BinLeafBoundedLength.parse_length_test_cost tag width entry.1
    change (BinLeafBoundedLength.parse tag width entry.1).2 +
      (leaves tag width rest).2 ≤ (rest.length + 1) * (width + 34)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- A fixed width gives a single linear polynomial for this component.
Rejected entries and duplicate occurrences are included. -/
theorem leaves_bounded_log (tag : Byte) (width Q : Nat) (log : Log)
    (hl : log.length ≤ Q + 1161) :
    (leaves tag width log).2 ≤ (width + 34) * (Q + 1161) := by
  have h := (leaves_length_test_cost tag width log).trans
    (Nat.mul_le_mul_right (width + 34) hl)
  simpa only [Nat.mul_comm] using h

#print axioms leaves_value
#print axioms leaves_length_test_cost
#print axioms leaves_bounded_log
end AspisR1.BinLeafBoundedTable
