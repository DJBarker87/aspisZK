import WireBindingRecordCodec
import R1Z.WireLengthsR1PBin

/-! D79 extension to all three checkpoint-binding digest classes. The codec
is shared verbatim with soundness; the existing transcript and privacy roots
are unchanged. Executed tx1 membership remains the R-wire refinement. -/
set_option autoImplicit false
namespace R1Z.WireBindingLengthsR1PBin
open AspisR1.WireBindingRecordCodec
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1 R1Z.LayoutR1PBin

/-- The checksum constructor fixes the actual input width, not a supplied
length inequality. All possible payload byte contents are covered. -/
theorem binding_fixed_length (r : BindingRecord) :
    r.bytes.length = 57607 ∨ r.bytes.length = 1880 ∨ r.bytes.length = 1758 := by
  rw [binding_length]
  cases r <;> simp [BindingRecord.kind, BindingClass.size, proof_bytes_eq, asf8_size_eq]

theorem node_ne_binding (answers : GamesR1PBin.RIdx → OracleAnswer)
    (ch : Fin 2 → GamesR1PBin.RIdx) (r : BindingRecord) :
    nodeBytes answers ch ≠ r.bytes := by
  intro he
  have hl := congrArg List.length he
  rw [nodeBytes_length] at hl
  exact (binding_safe r).1 hl.symm

theorem binding_ne_framed31 (r : BindingRecord) (frame : List UInt8)
    (hf : frame.length = 31) : r.bytes ≠ frame := by
  intro he
  exact (binding_safe r).2 ((congrArg List.length he).trans hf)

/-- Extension of the D79 concrete transcript carrier with checkpoint reads.
These inputs are additional verifier reads, not duplex transcript rows. -/
inductive ExtendedRead where
  | transcript (j : TRead) (answer : OracleAnswer)
  | binding (r : BindingRecord)

def ExtendedRead.bytes (w : WireLengthsR1PBin.Wire) : ExtendedRead → List UInt8
  | .transcript j f => addrWith j f (WireLengthsR1PBin.rest w)
  | .binding r => r.bytes

theorem node_ne_extended_read (w : WireLengthsR1PBin.Wire)
    (answers : GamesR1PBin.RIdx → OracleAnswer) (ch : Fin 2 → GamesR1PBin.RIdx)
    (read : ExtendedRead) : nodeBytes answers ch ≠ read.bytes w := by
  cases read with
  | transcript j f => exact WireLengthsR1PBin.node_ne_concrete_transcript w answers ch j f
  | binding r => exact node_ne_binding answers ch r

/-- Covers the entire tx1 site class table, including salted leaves. Node
reads are included in the table but cannot be separated from themselves. -/
theorem node_ne_classified_read (answers : GamesR1PBin.RIdx → OracleAnswer)
    (ch : Fin 2 → GamesR1PBin.RIdx) (c : Tx1Class) (hn : c ≠ .binaryNode)
    (bs : List UInt8) (hclass : bs.length = c.size) : nodeBytes answers ch ≠ bs := by
  intro he
  have hl := congrArg List.length he
  rw [nodeBytes_length, hclass] at hl
  exact (tx1_class_safe c hn).1 hl.symm

#print axioms binding_fixed_length
#print axioms node_ne_binding
#print axioms binding_ne_framed31
#print axioms node_ne_extended_read
#print axioms node_ne_classified_read
end R1Z.WireBindingLengthsR1PBin
