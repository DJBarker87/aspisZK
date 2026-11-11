import WireBindingRecordCodec
import R1SemanticPublicCodecComplete

/-! PIN2 W3b (2026-11-11). Ties the transcript-record size table to the parser:
the init frame of every parsed public statement has exactly the size the table
assigns to its class, so the 1595/1599 constants are not free.  Also checks
that every TX1 record class fits the selected duplex length L = 131072 and that
the two init classes are still told apart from every other class by length. -/
set_option autoImplicit false
namespace AspisR1.PIN2_Tx1InitRecordSize
open WireBindingRecordCodec

/-- The init class of a parsed statement. -/
def initClass (pub : R0P.Public SemanticPublicWire.M31) : Tx1Class :=
  if pub.variant = .privateTransfer then .initTransfer else .initWithdrawal

theorem init_frame_size (bytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (h : SemanticPublicWire.parsePublic bytes = some pub)
    (c1 : AspisV8R19.SourceDuplexStep.State) :
    (PublicInitFrame.frame bytes c1).length = (initClass pub).size := by
  rw [SemanticPublicCodecComplete.parsed_init_frame_length bytes pub h c1, initClass]
  split <;> rfl

theorem init_sizes : Tx1Class.size .initTransfer = 75 + 1520 ∧
    Tx1Class.size .initWithdrawal = 75 + 1524 := ⟨rfl, rfl⟩

/-- Every TX1 record class fits the selected duplex length 131072
(`SelectedTranscriptParams.L`); the largest is the compact proof, 57607. -/
theorem size_le_L (c : Tx1Class) : c.size ≤ 131072 := by
  cases c <;> simp only [Tx1Class.size] <;> try omega
  rename_i k
  cases k <;> simp only [BindingClass.size, proof_bytes_eq, asf8_size_eq] <;> omega

/-- The two init sizes are distinct from each other and from every other class. -/
theorem init_transfer_size_unique (c : Tx1Class) (h : c.size = 1595) : c = .initTransfer := by
  cases c <;> simp only [Tx1Class.size] at h <;> try omega
  · rfl
  · rename_i k
    cases k <;> simp only [BindingClass.size, proof_bytes_eq, asf8_size_eq] at h <;> omega

theorem init_withdrawal_size_unique (c : Tx1Class) (h : c.size = 1599) : c = .initWithdrawal := by
  cases c <;> simp only [Tx1Class.size] at h <;> try omega
  · rfl
  · rename_i k
    cases k <;> simp only [BindingClass.size, proof_bytes_eq, asf8_size_eq] at h <;> omega

#print axioms init_frame_size
#print axioms init_sizes
#print axioms size_le_L
#print axioms init_transfer_size_unique
#print axioms init_withdrawal_size_unique
end AspisR1.PIN2_Tx1InitRecordSize
