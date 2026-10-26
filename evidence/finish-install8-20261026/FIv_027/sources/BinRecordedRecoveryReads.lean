import BinMerkleRecoveryReads
import RawCutRecordedWordsBoundedBin
import RawRecordedLogCostObstruction

/-! A fused table pass and repeated recovery accounting. Each inspected log
or table record is charged, including repeats; bytes and arithmetic remain
separate. No completeness of the whole extractor call schedule is assumed. -/
set_option autoImplicit false
namespace AspisR1.BinRecordedRecoveryReads
open BinMerkle32Path BinMerkleTable
open BinMerkleLeafRecovery (LeafData Leaves)
open BinMerkleRecordedLog (Log)

def tables (tag : Byte) (width : Nat) : Log → (Nodes × Leaves) × Nat
  | [] => (([], []), 0)
  | (input, digest) :: rest =>
    let tail := tables tag width rest
    let node := BinMerkleNodeCodec.parse input
    let leaf := (BinLeafBoundedLength.parse tag width input).1
    ((match node with | none => tail.1.1 | some cs => (cs, digest) :: tail.1.1,
      match leaf with | none => tail.1.2 | some data => (data, digest) :: tail.1.2),
      tail.2 + 1)

theorem tables_value (tag : Byte) (width : Nat) (log : Log) :
    (tables tag width log).1 =
      (BinMerkleRecordedLog.nodes log, BinMerkleRecordedLog.leaves tag width log) := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨input, digest⟩
    simp only [tables, ih, BinLeafBoundedLength.parse_value,
      BinMerkleRecordedLog.nodes, BinMerkleRecordedLog.leaves, List.filterMap_cons]
    cases BinMerkleNodeCodec.parse input <;> cases BinMerkleLeafCodec.parse tag width input <;>
      rfl

theorem tables_reads (tag : Byte) (width : Nat) (log : Log) :
    (tables tag width log).2 = log.length := by
  induction log with
  | nil => rfl
  | cons entry rest ih => simp only [tables, ih, List.length_cons]

theorem tables_sizes (tag : Byte) (width : Nat) (log : Log) :
    (tables tag width log).1.1.length ≤ log.length ∧
    (tables tag width log).1.2.length ≤ log.length := by
  rw [tables_value]
  exact ⟨List.length_filterMap_le _ _, List.length_filterMap_le _ _⟩

def recover (tag : Byte) (width : Nat) (log : Log)
    (slots : List (Fin 2)) (root : Digest) : Option LeafData × Nat :=
  let t := tables tag width log
  let r := BinMerkleRecoveryReads.recoverCount t.1.1 t.1.2 slots root
  (r.1, t.2 + r.2)

theorem recover_value (tag : Byte) (width : Nat) (log : Log)
    (slots : List (Fin 2)) (root : Digest) :
    (recover tag width log slots root).1 =
      RawCutRecordedWordsBoundedBin.recoverAtExec tag width log slots root := by
  simp only [recover, BinMerkleRecoveryReads.recoverCount_result, tables_value,
    RawCutRecordedWordsBoundedBin.recoverAtExec, BinLeafBoundedTable.leaves_value]

theorem recover_reads (tag : Byte) (width : Nat) (log : Log)
    (slots : List (Fin 2)) (root : Digest) :
    (recover tag width log slots root).2 ≤ (slots.length + 2) * log.length := by
  have h := BinMerkleRecoveryReads.recoverCount_cost
    (tables tag width log).1.1 (tables tag width log).1.2 slots root
  obtain ⟨hn, hl⟩ := tables_sizes tag width log
  have hs := Nat.add_le_add (Nat.mul_le_mul_left slots.length hn) hl
  change (tables tag width log).2 + _ ≤ _
  rw [tables_reads]
  calc
    _ ≤ log.length + (slots.length * log.length + log.length) :=
      Nat.add_le_add_left (h.trans hs) _
    _ = _ := by ring

/-- Cut scan, prefix copying and fused tables are all charged on each call. -/
def cutRecover (tag : Byte) (width : Nat) (log : Log)
    (frame : List Byte) (slots : List (Fin 2)) (root : Digest) :
    Option LeafData × Nat :=
  let cut := RawRecordedLogCostObstruction.cutBeforeWithReads log frame
  let r := recover tag width cut.1 slots root
  (r.1, cut.2 + cut.1.length + r.2)

theorem cutRecover_value (tag : Byte) (width : Nat) (log : Log)
    (frame : List Byte) (slots : List (Fin 2)) (root : Digest) :
    (cutRecover tag width log frame slots root).1 =
      RawCutRecordedWordsBoundedBin.recoverAtExec tag width
        (RawCutRecordedWordsBoundedBin.cutBeforeExec log frame) slots root := by
  simp only [cutRecover, recover_value, RawRecordedLogCostObstruction.cutBeforeWithReads_value]

theorem cutRecover_reads (tag : Byte) (width : Nat) (log : Log)
    (frame : List Byte) (slots : List (Fin 2)) (root : Digest) :
    (cutRecover tag width log frame slots root).2 ≤ (slots.length + 4) * log.length := by
  let cut := RawRecordedLogCostObstruction.cutBeforeWithReads log frame
  have hc : cut.2 ≤ log.length :=
    RawRecordedLogCostObstruction.firstIndexWithReads_le_length frame log
  have hl : cut.1.length ≤ log.length := by
    dsimp [cut, RawRecordedLogCostObstruction.cutBeforeWithReads]
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hr := (recover_reads tag width cut.1 slots root).trans
    (Nat.mul_le_mul_left (slots.length + 2) hl)
  change cut.2 + cut.1.length + _ ≤ _
  calc
    _ ≤ log.length + log.length + (slots.length + 2) * log.length :=
      Nat.add_le_add (Nat.add_le_add hc hl) hr
    _ = _ := by ring

structure Request where
  tag : Byte
  width : Nat
  frame : List Byte
  slots : List (Fin 2)
  root : Digest

def batch (log : Log) : List Request → List (Option LeafData) × Nat
  | [] => ([], 0)
  | r :: rest =>
    let head := cutRecover r.tag r.width log r.frame r.slots r.root
    let tail := batch log rest
    (head.1 :: tail.1, head.2 + tail.2)

theorem batch_value (log : Log) (rs : List Request) :
    (batch log rs).1 = rs.map (fun r =>
      RawCutRecordedWordsBoundedBin.recoverAtExec r.tag r.width
        (RawCutRecordedWordsBoundedBin.cutBeforeExec log r.frame) r.slots r.root) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [batch, List.map_cons, cutRecover_value, ih]

/-- Repeated requests incur repeated scans and are never deduplicated here. -/
theorem batch_reads (log : Log) (rs : List Request)
    (hd : ∀ r ∈ rs, r.slots.length ≤ 18) :
    (batch log rs).2 ≤ rs.length * (22 * log.length) := by
  induction rs with
  | nil => simp [batch]
  | cons r rs ih =>
    have hh := (cutRecover_reads r.tag r.width log r.frame r.slots r.root).trans
      (Nat.mul_le_mul_right log.length (Nat.add_le_add_right (hd r List.mem_cons_self) 4))
    have ht := ih (fun r hr => hd r (List.mem_cons_of_mem _ hr))
    change _ + _ ≤ _
    calc
      _ ≤ 22 * log.length + rs.length * (22 * log.length) := Nat.add_le_add hh ht
      _ = _ := by simp only [List.length_cons]; ring

theorem batch_bounded_log (log : Log) (rs : List Request) (Q calls : Nat)
    (hd : ∀ r ∈ rs, r.slots.length ≤ 18)
    (hl : log.length ≤ Q + 1161) (hc : rs.length ≤ calls) :
    (batch log rs).2 ≤ 22 * calls * (Q + 1161) := by
  have h := (batch_reads log rs hd).trans
    (Nat.mul_le_mul hc (Nat.mul_le_mul_left 22 hl))
  exact h.trans (le_of_eq (by ring))

#print axioms tables_value
#print axioms tables_reads
#print axioms tables_sizes
#print axioms recover_value
#print axioms recover_reads
#print axioms cutRecover_value
#print axioms cutRecover_reads
#print axioms batch_value
#print axioms batch_reads
#print axioms batch_bounded_log
end AspisR1.BinRecordedRecoveryReads
