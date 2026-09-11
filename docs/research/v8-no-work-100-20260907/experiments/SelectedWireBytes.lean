import CanonicalRelationInput
import PackedQueryRecord

/-!
Exact selected 697-field / q22 Wire layout as a pure byte-list parser.
It reuses the checked fixed-field parser and therefore its length guard and
canonical decoding. Successful parsing proves that the totalized byte reads
below are in bounds. This is not a Rust/Aeneas translation, authentication
theorem, or transcript-order/freshness statement.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedWireBytes
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCQM31Representation
open AspisPool.V7MerkleQueryGrammar

abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte

def slice (body : List Byte) (start count : Nat) : List Byte :=
  (body.drop start).take count

theorem slice_length (body : List Byte) (start count : Nat)
    (bounded : start + count ≤ body.length) :
    (slice body start count).length = count := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem slice_byte (body : List Byte) (start count byte : Nat)
    (bounded : start + count ≤ body.length) (inside : byte < count) :
    (slice body start count).getD byte 0 = body.getD (start + byte) 0 := by
  have localBound : byte < (slice body start count).length := by
    rw [slice_length body start count bounded]
    exact inside
  rw [List.getD_eq_getElem _ _ localBound,
    List.getD_eq_getElem _ _ (by omega : start + byte < body.length)]
  simp only [slice, List.getElem_take, List.getElem_drop]

/-- Each frontier has half the bytes remaining after the 22 records. -/
def halfFrontier (body : List Byte) : Nat := (body.length - 24890) / 2

structure Wire where
  values : List K
  roots : Fin 2 → Digest208
  nonces : List Byte
  records : List Byte
  frontiers : Fin 2 → List Byte

def assemble (body : List Byte) (values : List K) : Wire where
  values := values
  roots := fun phase byte => body.getD (11152 + 26 * phase.val + byte.val) 0
  nonces := slice body 11204 24
  records := slice body 11228 13662
  frontiers := fun phase =>
    slice body (24890 + phase.val * halfFrontier body) (halfFrontier body)

/-- Unlike a record parser this does not decode packed query limbs: Rust's
Wire parser also defers that canonicality check to opened_values_prepared. -/
def parse (body : List Byte) : Option Wire :=
  (CanonicalRelationInput.parseFixed body).map (assemble body)

theorem parse_success (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    CanonicalRelationInput.parseFixed body = some wire.values ∧
      wire = assemble body wire.values := by
  cases fixed : CanonicalRelationInput.parseFixed body with
  | none => simp only [parse, fixed, Option.map_none] at success; cases success
  | some values =>
      have same : assemble body values = wire := by
        simpa only [parse, fixed, Option.map_some, Option.some.injEq] using success
      subst wire
      exact ⟨rfl, rfl⟩

theorem malformed_length (body : List Byte)
    (bad : CanonicalRelationInput.badLength body.length) : parse body = none := by
  simp only [parse, CanonicalRelationInput.malformed_length body bad, Option.map_none]

theorem successful_length (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    ∃ count : Nat, count ≤ 296 ∧ body.length = 24890 + 52 * count ∧
      halfFrontier body = 26 * count := by
  obtain ⟨count, cap, shape⟩ := (CanonicalRelationInput.length_shape body.length).mp
    (CanonicalRelationInput.parse_success body wire.values
      (parse_success body wire success).1).1
  refine ⟨count, cap, shape, ?_⟩
  unfold halfFrontier
  omega

theorem fixed_fields (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    wire.values.length = 697 ∧ ∀ field : Fin 697,
      decodeQM31ExactLE (CanonicalRelationInput.fieldBytes body field) =
        some (wire.values.getD field.val 0) :=
  (CanonicalRelationInput.parse_success body wire.values
    (parse_success body wire success).1).2

theorem root_in_bounds (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (phase : Fin 2) (byte : Fin 26) :
    11152 + 26 * phase.val + byte.val < body.length := by
  obtain ⟨count, _, shape, _⟩ := successful_length body wire success
  have hp := phase.isLt
  have hb := byte.isLt
  omega

/-- Both roots are the literal input bytes, not merely equal to another
independently supplied root. Phase 0 starts at 11152, phase 1 at 11178. -/
theorem roots_exact (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (phase : Fin 2) (byte : Fin 26) :
    wire.roots phase byte =
      body[11152 + 26 * phase.val + byte.val]'(root_in_bounds body wire success phase byte) := by
  have projected : wire.roots phase byte =
      body.getD (11152 + 26 * phase.val + byte.val) 0 :=
    congrArg (fun w : Wire => w.roots phase byte) (parse_success body wire success).2
  exact projected.trans (List.getD_eq_getElem _ _
    (root_in_bounds body wire success phase byte))

theorem fixed_slice_lengths (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    wire.nonces.length = 24 ∧ wire.records.length = 22 * 621 := by
  obtain ⟨count, _, shape, _⟩ := successful_length body wire success
  rw [(parse_success body wire success).2]
  exact ⟨slice_length body 11204 24 (by omega),
    slice_length body 11228 13662 (by omega)⟩

/-- Nonces are gamma/fold/query at offsets 11204,11212,11220; no
endianness interpretation or successful grinding predicate is introduced. -/
theorem nonce_byte (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (nonce : Fin 3) (byte : Fin 8) :
    wire.nonces.getD (8 * nonce.val + byte.val) 0 =
      body.getD (11204 + 8 * nonce.val + byte.val) 0 := by
  obtain ⟨count, _, shape, _⟩ := successful_length body wire success
  have hn := nonce.isLt
  have hb := byte.isLt
  rw [(parse_success body wire success).2]
  simpa only [assemble, Nat.add_assoc] using
    slice_byte body 11204 24 (8 * nonce.val + byte.val) (by omega) (by omega)

def Wire.record (wire : Wire) (query : Fin 22) : List Byte :=
  List.ofFn fun byte : Fin 621 => wire.records.getD (621 * query.val + byte.val) 0

/-- No record ordinal is sorted or relabelled by this byte projection. -/
theorem record_byte (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (query : Fin 22) (byte : Fin 621) :
    wire.records.getD (621 * query.val + byte.val) 0 =
      body.getD (11228 + 621 * query.val + byte.val) 0 := by
  obtain ⟨count, _, shape, _⟩ := successful_length body wire success
  have hq := query.isLt
  have hb := byte.isLt
  rw [(parse_success body wire success).2]
  simpa only [assemble, Nat.add_assoc] using
    slice_byte body 11228 13662 (621 * query.val + byte.val) (by omega) (by omega)

theorem record_eq_bodyRecord (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (query : Fin 22) :
    wire.record query = PackedQueryRecord.bodyRecord body query := by
  unfold Wire.record PackedQueryRecord.bodyRecord
  apply congrArg List.ofFn
  funext byte
  exact record_byte body wire success query byte

theorem record_bytes_exact (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (query : Fin 22) (byte : Fin 621) :
    (wire.record query).getD byte.val 0 =
      body[11228 + 621 * query.val + byte.val]'
        (PackedQueryRecord.body_record_in_bounds body wire.values
          (parse_success body wire success).1 query byte) := by
  rw [record_eq_bodyRecord body wire success query]
  exact PackedQueryRecord.bodyRecord_byte_exact body wire.values
    (parse_success body wire success).1 query byte

theorem frontier_lengths (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    ∃ count : Nat, count ≤ 296 ∧ halfFrontier body = 26 * count ∧
      ∀ phase : Fin 2, (wire.frontiers phase).length = 26 * count := by
  obtain ⟨count, cap, shape, half⟩ := successful_length body wire success
  refine ⟨count, cap, half, ?_⟩
  intro phase
  have bounded : 24890 + phase.val * halfFrontier body + halfFrontier body ≤
      body.length := by
    fin_cases phase <;> simp only [zero_mul, one_mul, Nat.add_zero] <;> omega
  rw [(parse_success body wire success).2]
  exact (slice_length body _ _ bounded).trans half

/-- The second slice reaches the exact end, as Rust's final open-ended
slice does; the accepted length guard prevents a discarded trailing byte. -/
theorem second_frontier_to_end (body : List Byte) (wire : Wire)
    (success : parse body = some wire) :
    wire.frontiers 1 = body.drop (24890 + halfFrontier body) := by
  obtain ⟨count, _, shape, half⟩ := successful_length body wire success
  rw [(parse_success body wire success).2]
  change slice body (24890 + 1 * halfFrontier body) (halfFrontier body) = _
  simp only [one_mul, slice]
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

theorem frontier_byte (body : List Byte) (wire : Wire)
    (success : parse body = some wire) (phase : Fin 2) (byte : Nat)
    (inside : byte < halfFrontier body) :
    (wire.frontiers phase).getD byte 0 =
      body.getD (24890 + phase.val * halfFrontier body + byte) 0 := by
  obtain ⟨count, _, shape, half⟩ := successful_length body wire success
  have bounded : 24890 + phase.val * halfFrontier body + halfFrontier body ≤
      body.length := by
    fin_cases phase <;> simp only [zero_mul, one_mul, Nat.add_zero] <;> omega
  rw [(parse_success body wire success).2]
  exact slice_byte body _ _ byte bounded inside

/-- Typed paired digests, aligned by one shared ordinal across both trees.
Success below proves the count and that every byte belongs to its own half. -/
def Wire.frontierPairs (wire : Wire) : List (Fin 2 → Digest208) :=
  List.ofFn fun item : Fin ((wire.frontiers 0).length / 26) =>
    fun phase byte => (wire.frontiers phase).getD (26 * item.val + byte.val) 0

theorem frontier_pairs_length (body : List Byte) (wire : Wire)
    (success : parse body = some wire) : wire.frontierPairs.length ≤ 296 := by
  obtain ⟨count, cap, _, lengths⟩ := frontier_lengths body wire success
  simp only [Wire.frontierPairs, List.length_ofFn, lengths 0]
  omega

theorem frontier_pair_byte (body : List Byte) (wire : Wire)
    (success : parse body = some wire)
    (item : Fin ((wire.frontiers 0).length / 26)) (phase : Fin 2) (byte : Fin 26) :
    (wire.frontierPairs[item.val]'(by
      simpa only [Wire.frontierPairs, List.length_ofFn] using item.isLt)) phase byte =
      body.getD (24890 + phase.val * halfFrontier body + 26 * item.val + byte.val) 0 := by
  obtain ⟨count, _, half, lengths⟩ := frontier_lengths body wire success
  have countExact : (wire.frontiers 0).length / 26 = count := by
    rw [lengths 0]
    omega
  have hi : item.val < count := item.isLt.trans_le countExact.le
  have hb := byte.isLt
  simp only [Wire.frontierPairs, List.getElem_ofFn]
  simpa only [Nat.add_assoc] using
    frontier_byte body wire success phase (26 * item.val + byte.val) (by omega)

#print axioms slice_length
#print axioms slice_byte
#print axioms parse_success
#print axioms malformed_length
#print axioms successful_length
#print axioms fixed_fields
#print axioms roots_exact
#print axioms fixed_slice_lengths
#print axioms nonce_byte
#print axioms record_eq_bodyRecord
#print axioms record_bytes_exact
#print axioms frontier_lengths
#print axioms second_frontier_to_end
#print axioms frontier_byte
#print axioms frontier_pairs_length
#print axioms frontier_pair_byte
end
end AspisV8.SelectedWireBytes
