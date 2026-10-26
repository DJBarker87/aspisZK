import BinFrameSizeBound
import BinLeafListWork

/-! Last-write replay with byte comparisons on the bounded query side.
This counts comparisons and replay visits, including unsuccessful lookups.
It does not charge constructing the query or the surrounding frame schedule. -/
set_option autoImplicit false
namespace AspisR1.BinFrameLookupWork
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8PairedCommitment FS FS2.Duplex

def lookup (a : Bytes) : Option State → List (Bytes × State) → Option State × Nat
  | current, [] => (current, 1)
  | current, (i, v) :: rest =>
    let eq := BinLeafListWork.equal a i
    let r := lookup a (if eq.1 then some v else current) rest
    (r.1, eq.2 + 3 + r.2)

theorem lookup_value (a : Bytes) (current : Option State) (log : List (Bytes × State)) :
    (lookup a current log).1 = (BinFrameReplayReads.lookup a current log).1 := by
  induction log generalizing current with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨i, v⟩
    simp only [lookup, BinLeafListWork.equal_value, decide_eq_true_eq,
      BinFrameReplayReads.lookup, ih]

theorem lookup_work (a : Bytes) (current : Option State) (log : List (Bytes × State)) :
    (lookup a current log).2 ≤ (2 * a.length + 4) * log.length + 1 := by
  induction log generalizing current with
  | nil => simp only [lookup, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons entry rest ih =>
    rcases entry with ⟨i, v⟩
    have he := BinLeafListWork.equal_work a i
    have hr := ih (if (BinLeafListWork.equal a i).1 then some v else current)
    change _ + 3 + _ ≤ _
    rw [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def oracle (log : List (Bytes × State)) (a : Bytes) : State × Nat :=
  let r := lookup a none log
  (r.1.getD default, r.2 + 1)

theorem oracle_value (log : List (Bytes × State)) (a : Bytes) :
    (oracle log a).1 = OracleProgramReplay.oracleOf log a := by
  change (lookup a none log).1.getD default = _
  rw [lookup_value]
  exact BinFrameReplayReads.oracle_value log a

theorem oracle_work (log : List (Bytes × State)) (a : Bytes)
    (ha : a.length ≤ 131072) :
    (oracle log a).2 ≤ 262148 * log.length + 2 := by
  have h := lookup_work a none log
  have hm := Nat.mul_le_mul_right log.length
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 4)
  change _ + 1 ≤ _
  omega

/-- All three short successor query classes also fit the same bound. -/
theorem short_lengths (state : State) (tag : Byte) :
    (RawTranscriptFrameBytes.rowZero state).length ≤ 131072 ∧
    (RawTranscriptFrameBytes.advance state).length ≤ 131072 ∧
    (RawTranscriptFrameBytes.reseed tag state).length ≤ 131072 := by
  simp only [RawTranscriptFrameBytes.rowZero, RawTranscriptFrameBytes.advance,
    RawTranscriptFrameBytes.reseed, RawTranscriptFrameBytes.openingDomain,
    List.length_append, bytes_length, List.length_cons, List.length_nil]
  omega

#print axioms lookup_value
#print axioms lookup_work
#print axioms oracle_value
#print axioms oracle_work
#print axioms short_lengths
end AspisR1.BinFrameLookupWork
