import BinNodeListWork
import BinRecordedRecoveryReads

/-! Fused binary node/leaf construction with bounded byte work and cumulative
allocation work. The added constant covers per-entry destructuring, option,
pair and output cons allocation. Inputs are referenced rather than deep copied.
The table's unrestricted source keys are never measured by input byte length. -/
set_option autoImplicit false
namespace AspisR1.BinTableWork
open BinMerkle32Path BinMerkleTable
open BinMerkleLeafRecovery (Leaves)
open BinMerkleRecordedLog (Log)

def tables (tag : Byte) (width : Nat) : Log → (Nodes × Leaves) × Nat
  | [] => (([], []), 1)
  | (input, digest) :: rest =>
    let tail := tables tag width rest
    let node := BinNodeListWork.parse input
    let leaf := BinLeafListWork.parse tag width input
    ((match node.1 with | none => tail.1.1 | some cs => (cs, digest) :: tail.1.1,
      match leaf.1 with | none => tail.1.2 | some data => (data, digest) :: tail.1.2),
      tail.2 + node.2 + leaf.2 + 32)

theorem tables_value (tag : Byte) (width : Nat) (log : Log) :
    (tables tag width log).1 = (BinRecordedRecoveryReads.tables tag width log).1 := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨input, digest⟩
    simp only [tables, BinRecordedRecoveryReads.tables, ih,
      BinNodeListWork.parse_value, BinLeafListWork.parse_value,
      BinLeafBoundedLength.parse_value]
    rfl

theorem tables_work (tag : Byte) (width : Nat) (log : Log) :
    (tables tag width log).2 ≤ log.length * (8 * width + 4704) + 1 := by
  induction log with
  | nil => simp only [tables, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | cons entry rest ih =>
    rcases entry with ⟨input, digest⟩
    have hn := BinNodeListWork.parse_work input
    have hl := BinLeafListWork.parse_work tag width input
    change _ + _ + _ + 32 ≤ _
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A fixed 512-bit slot accounting for byte/list/option/pair cells. This is
an explicit abstract fixed-slot model, not a theorem about Lean's heap or
unbounded Nat pointer addresses. Total allocated slots bound peak retained
slots without needing a garbage collector model. -/
def allocatedBits (tag : Byte) (width : Nat) (log : Log) : Nat :=
  512 * (tables tag width log).2

theorem allocated_bits_bound (tag : Byte) (width : Nat) (log : Log) :
    allocatedBits tag width log ≤ 512 * (log.length * (8 * width + 4704) + 1) :=
  Nat.mul_le_mul_left _ (tables_work tag width log)

theorem fixed_width_work (tag : Byte) (width : Nat) (log : Log)
    (hw : width ≤ 480) : (tables tag width log).2 ≤ 8544 * log.length + 1 := by
  have h := (tables_work tag width log).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left log.length
      (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hw) 4704)) 1)
  simpa only [Nat.mul_comm log.length] using h

#print axioms tables_value
#print axioms tables_work
#print axioms allocated_bits_bound
#print axioms fixed_width_work
end AspisR1.BinTableWork
