import SelectedWireBytes

/-! Source-shaped fixed-byte cursor loop, independently related to the
functional finite-field parser. Rust source: relation_callback.rs::parse
(`b[..697*16].chunks_exact(16).map(QM31::from_le_bytes).collect`).
The loop below is NOT an Aeneas/LLVM extraction: Rust slice/iterator/compiler
semantics and the field.rs decoder-to-decodeQM31ExactLE translation remain
explicit boundaries. The theorem does not assume EncodedCausalFields, a
semantic Program, a caller-provided recovered table, or acceptance.
Packed-record canonicality remains deferred just as in the Wire parser.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
namespace AspisV8.SameBodyChunkParser
open AspisV5ComponentCQM31Representation AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open AspisPool.V7MerkleQueryGrammar
noncomputable section
abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte

/-- One literal 16-byte chunk at the current byte cursor. Totalized access
is removed by the successful length guard in `chunk_in_bounds`. -/
def chunk (body : List Byte) (offset : Nat) : QM31Bytes :=
  fun byte => body.getD (offset + byte.val) 0

/-- Short-circuit, left-to-right, one decoded field per 16-byte advance.
Neither `List.ofFn` nor CanonicalCollect occurs in this producer. -/
def cursor (body : List Byte) (offset : Nat) : Nat → Option (List K)
  | 0 => some []
  | n+1 => do
    let value ← decodeQM31ExactLE (chunk body offset)
    let rest ← cursor body (offset+16) n
    pure (value::rest)

theorem cursor_eq_collect (body : List Byte) (n offset : Nat) :
    cursor body offset n = CanonicalCollect.collect decodeQM31ExactLE
      (List.ofFn (fun i : Fin n => chunk body (offset+16*i.val))) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [cursor, CanonicalCollect.collect, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
    rw [ih]
    have offsets : (fun i : Fin n => chunk body (offset+16+16*i.val)) =
        (fun i : Fin n => chunk body (offset+16*i.succ.val)) := by
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega
    rw [offsets]

/-- Verbatim source guard, retaining the HEAD and record-size arithmetic. -/
def sourceBadLength (n : Nat) : Prop :=
  n < (697*16+52+24)+22*621 ∨ 40282 < n ∨
    (n-(697*16+52+24)-22*621)%52 ≠ 0

instance (n : Nat) : Decidable (sourceBadLength n) := by
  unfold sourceBadLength
  infer_instance

theorem source_guard_eq (n : Nat) : sourceBadLength n ↔ CanonicalRelationInput.badLength n := by
  rfl

def fields (body : List Byte) : Option (List K) :=
  if sourceBadLength body.length then none else cursor body 0 697

theorem fields_eq_parseFixed (body : List Byte) :
    fields body = CanonicalRelationInput.parseFixed body := by
  have chunks : (fun i : Fin 697 => chunk body (0+16*i.val)) =
      CanonicalRelationInput.fieldBytes body := by
    funext i byte
    simp only [chunk, CanonicalRelationInput.fieldBytes, Nat.zero_add]
  unfold fields CanonicalRelationInput.parseFixed
  rw [cursor_eq_collect, chunks]
  rfl

def wire (body : List Byte) : Option SelectedWireBytes.Wire :=
  (fields body).map (SelectedWireBytes.assemble body)

/-- Includes both roots/nonces/records/frontiers because the same successful
field list is passed to the independently defined literal slice assembly. -/
theorem wire_eq_parse (body : List Byte) : wire body = SelectedWireBytes.parse body := by
  unfold wire SelectedWireBytes.parse
  rw [fields_eq_parseFixed]

theorem accepted_fields (body : List Byte) (values : List K)
    (success : fields body = some values) :
    ¬sourceBadLength body.length ∧ values.length = 697 ∧
      ∀ i : Fin 697, decodeQM31ExactLE (chunk body (16*i.val)) =
        some (values.getD i.val 0) := by
  rw [fields_eq_parseFixed] at success
  exact CanonicalRelationInput.parse_success body values success

theorem chunk_in_bounds (body : List Byte) (values : List K)
    (success : fields body = some values) (i : Fin 697) (byte : Fin 16) :
    16*i.val+byte.val < body.length := by
  rw [fields_eq_parseFixed] at success
  exact CanonicalRelationInput.success_in_bounds body values success i byte

theorem malformed_length (body : List Byte) (bad : sourceBadLength body.length) :
    fields body = none := by
  unfold fields
  exact if_pos bad

theorem rejected_limb (body : List Byte) (i : Fin 697) (limb : Fin 4)
    (high : m31Modulus ≤ (decodeWordLE (qm31LimbBytes (chunk body (16*i.val)) limb)).val) :
    fields body = none := by
  rw [fields_eq_parseFixed]
  exact CanonicalRelationInput.noncanonical_reject body i limb high

/-- All seven hundred-minus-three source decodes are covered symbolically:
no giant finite enumeration or concrete QM31 computation is used. -/
theorem guard_frontier_shape (n : Nat) :
    ¬sourceBadLength n ↔ ∃ frontier : Nat, frontier ≤ 296 ∧ n=24890+52*frontier :=
  CanonicalRelationInput.length_shape n

#print wire_eq_parse
#print axioms cursor_eq_collect
#print axioms fields_eq_parseFixed
#print axioms wire_eq_parse
#print axioms accepted_fields
#print axioms chunk_in_bounds
#print axioms rejected_limb
#print axioms guard_frontier_shape
end
end AspisV8.SameBodyChunkParser
