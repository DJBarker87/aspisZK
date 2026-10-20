import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! Source-shaped byte widths for the three checkpoint digest inputs.
This is a codec model, not an extraction of checkpoint or whole tx1.
Source pins are in design/WIRE-LENGTHS-ADDENDUM-20261020.md. -/
set_option autoImplicit false
namespace AspisR1.WireBindingRecordCodec

/-- compact.rs:26–50,69: offsets, compact values, and six padded node slots. -/
def proof_bytes : Nat :=
  16 + ((12903 + 29 * 32) - 16 * (1 + 10 * 28 + (87 + 29) + 29)) +
  29 * 16 + 32 + 224 + 32 + 224 + 64 * 32 +
  22 * (480 + 128 + 32 + 32 + 128 + 32) + 32 * (2 * (146 + 172) + (128 + 150))

/-- ASF8 header, late statement and payment; pair_forest_terminal.rs:33. -/
def asf8_size : Nat := 144 + 1520 + 216

theorem proof_bytes_eq : proof_bytes = 57607 := by rfl
theorem asf8_size_eq : asf8_size = 1880 := by rfl

/-- The fields appended before the checksum, verifier.rs:273–283.
Wide values occupy 32 bytes; K values 16; S2 has 64 weights. -/
structure CheckpointBody (Byte : Type) where
  header : Vector Byte 16
  proofHash : Vector Byte 32
  publicHash : Vector Byte 32
  state : Vector Byte 32
  roots : Vector Byte (2 * 32)
  challenges : Vector Byte (4 * 32)
  rho : Vector Byte 16
  queries : Vector Byte (22 * 4)
  semanticAlpha : Vector Byte (10 * 16)
  z : Vector Byte (2 * 2 * 16)
  claimRhs : Vector Byte (2 * 32)
  power : Vector Byte 16
  weights : Vector Byte (64 * 16)

def CheckpointBody.bytes {Byte : Type} (b : CheckpointBody Byte) : List Byte :=
  b.header.toList ++ b.proofHash.toList ++ b.publicHash.toList ++ b.state.toList ++
  b.roots.toList ++ b.challenges.toList ++ b.rho.toList ++ b.queries.toList ++
  b.semanticAlpha.toList ++ b.z.toList ++ b.claimRhs.toList ++ b.power.toList ++ b.weights.toList

theorem checkpoint_body_length {Byte : Type} (b : CheckpointBody Byte) :
    b.bytes.length = 1736 := by simp [CheckpointBody.bytes]

/-- Literal 22-byte ASCII domain, followed by the body (no trailing checksum). -/
def checksumDomain : List UInt8 :=
  [85,78,80,82,79,86,69,68,58,82,49,58,99,104,101,99,107,112,111,105,110,116]

theorem checksum_domain_bytes :
    checksumDomain = "UNPROVED:R1:checkpoint".toUTF8.toList := by rfl

def checksumInput (b : CheckpointBody UInt8) : List UInt8 := checksumDomain ++ b.bytes

theorem checksum_input_length (b : CheckpointBody UInt8) :
    (checksumInput b).length = 1758 := by
  simp [checksumInput, checksumDomain, checkpoint_body_length]

inductive BindingClass where
  | compactProof | asf8Account | checkpointChecksum
  deriving DecidableEq

def BindingClass.size : BindingClass → Nat
  | .compactProof => proof_bytes
  | .asf8Account => asf8_size
  | .checkpointChecksum => 1758

/-- Each constructor is the actual binding input, rather than its hash output. -/
inductive BindingRecord where
  | compactProof (bytes : Vector UInt8 proof_bytes)
  | asf8Account (bytes : Vector UInt8 asf8_size)
  | checkpointChecksum (body : CheckpointBody UInt8)

def BindingRecord.kind : BindingRecord → BindingClass
  | .compactProof _ => .compactProof
  | .asf8Account _ => .asf8Account
  | .checkpointChecksum _ => .checkpointChecksum

def BindingRecord.bytes : BindingRecord → List UInt8
  | .compactProof bytes => bytes.toList
  | .asf8Account bytes => bytes.toList
  | .checkpointChecksum body => checksumInput body

theorem binding_length (r : BindingRecord) : r.bytes.length = r.kind.size := by
  cases r <;> simp [BindingRecord.bytes, BindingRecord.kind, BindingClass.size,
    checksum_input_length]

theorem binding_safe (r : BindingRecord) : r.bytes.length ≠ 65 ∧ r.bytes.length ≠ 31 := by
  rw [binding_length]
  cases r <;> simp [BindingRecord.kind, BindingClass.size, proof_bytes_eq, asf8_size_eq]

/-- All digest-site classes in the WIRE-TX1 inventory. Several sites share a
class. Binary node is deliberately included and is exempt from self-separation. -/
inductive Tx1Class where
  | initTransfer | initWithdrawal | semanticEmpty | semanticRoot | semanticCoefficients
  | circleClaims | circleBefore | openingY1 | openingInactive | openingFirst
  | openingFolded | openingFinal | openingEmpty | reseed | read
  | leafC1 | leafSmall | binaryNode | binding (kind : BindingClass)
  deriving DecidableEq

def Tx1Class.size : Tx1Class → Nat
  | .initTransfer => 1530 | .initWithdrawal => 1502
  | .semanticEmpty => 39 | .semanticRoot => 71 | .semanticCoefficients => 935
  | .circleClaims => 3751 | .circleBefore => 967
  | .openingY1 => 966 | .openingInactive => 70 | .openingFirst => 262
  | .openingFolded => 294 | .openingFinal => 2086 | .openingEmpty => 38
  | .reseed => 62 | .read => 33 | .leafC1 => 514 | .leafSmall => 162
  | .binaryNode => 65 | .binding k => k.size

theorem tx1_class_safe (c : Tx1Class) (hn : c ≠ .binaryNode) :
    c.size ≠ 65 ∧ c.size ≠ 31 := by
  cases c <;> simp_all [Tx1Class.size]
  rename_i k
  cases k <;> simp [BindingClass.size, proof_bytes_eq, asf8_size_eq]

#print axioms proof_bytes_eq
#print axioms asf8_size_eq
#print axioms checkpoint_body_length
#print axioms checksum_domain_bytes
#print axioms checksum_input_length
#print axioms binding_length
#print axioms binding_safe
#print axioms tx1_class_safe
end AspisR1.WireBindingRecordCodec
