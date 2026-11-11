import JFs_SerializerLengths

/-! PIN2 W3b (2026-11-11): lengths and offsets of the PIN2 `public_bytes`.

W1's Rust (`43919c0a9f2`) keeps the frozen section-9 instruction sequence and
appends `pool[32]`, `deployment_domain[32]`, `has_destination` (1 iff
withdrawal) and, for a withdrawal, `destination_token_account[32]`.  This file
states the byte image of that body over the extracted public input structs,
factored as the unchanged prefix `sourceSteps` followed by the binding tail,
and proves its lengths and every write offset by named lemmas and small
arithmetic.

It does not prove that the re-extracted `public_bytes` produces `bytes q`:
that refinement (the PIN2 analogue of `NHG_Serializer.bytes` and
`Whole431.source_success`) needs Stream C's fresh extraction of the changed
body.  The `*_of_refines` theorems take it as an explicit hypothesis about
an arbitrary producer and are meant to be instantiated once it exists. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PIN2_SerializerLengths
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Whole431

theorem digest (a : Array U32 8#usize) : a.val.length = 8 := a.property
theorem index (n : U64) : (core.num.U64.to_le_bytes n).val.length = 8 :=
  (core.num.U64.to_le_bytes n).property
theorem raw32 (a : Array U8 32#usize) : a.val.length = 32 := a.property

/-- Frozen (4bb3b3f) section-9 bytes: the unchanged prefix of the PIN2 body. -/
def prefixBytes (q : Public) : List U8 := (sourceSteps q).flatMap stepBytes

def oldLength : Public → Nat
  | .Transfer _ _ => 1455
  | .Withdrawal _ _ => 1427

def pool : Public → Array U8 32#usize
  | .Transfer p _ => p.pool
  | .Withdrawal p _ => p.pool

def domain : Public → Array U8 32#usize
  | .Transfer p _ => p.deployment_domain
  | .Withdrawal p _ => p.deployment_domain

def destination : Public → Option (Array U8 32#usize)
  | .Transfer _ _ => none
  | .Withdrawal p _ => some p.destination_token_account

def hasDestination (q : Public) : U8 :=
  match destination q with
  | none => 0#u8
  | some _ => 1#u8

def destinationBytes (q : Public) : List U8 :=
  match destination q with
  | none => []
  | some d => d.val

/-- The appended binding tail, in W1's write order. -/
def tailBytes (q : Public) : List U8 :=
  (pool q).val ++ (domain q).val ++ [hasDestination q] ++ destinationBytes q

/-- The PIN2 `public_bytes` image. -/
def bytes (q : Public) : List U8 := prefixBytes q ++ tailBytes q

def newLength : Public → Nat
  | .Transfer _ _ => 1520
  | .Withdrawal _ _ => 1524

theorem prefix_length (q : Public) : (prefixBytes q).length = oldLength q := by
  cases q <;>
  simp only [prefixBytes, oldLength, sourceSteps, tailSteps, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.length_append, stepBytes,
    JFs_SerializerLengths.words, JFs_SerializerLengths.frontier_words, index,
    digest, single, Array.to_slice, Array.make, List.length_cons, List.length_nil]

theorem destination_length (q : Public) :
    (destinationBytes q).length = match q with | .Transfer _ _ => 0 | .Withdrawal _ _ => 32 := by
  cases q <;> simp only [destinationBytes, destination, List.length_nil, raw32]

theorem tail_length (q : Public) :
    (tailBytes q).length = match q with | .Transfer _ _ => 65 | .Withdrawal _ _ => 97 := by
  have hd := destination_length q
  cases q <;> simp only [tailBytes, List.length_append, raw32, List.length_singleton] at hd ⊢ <;>
    omega

theorem length (q : Public) : (bytes q).length = newLength q := by
  have hp := prefix_length q
  have ht := tail_length q
  cases q <;> simp only [bytes, newLength, oldLength, List.length_append] at hp ht ⊢ <;> omega

theorem bound (q : Public) : (bytes q).length ≤ 1524 := by
  rw [length]; cases q <;> simp only [newLength] <;> omega

/-- The frozen layout is a byte-identical prefix of the PIN2 body. -/
theorem prefix_preserved (q : Public) : (bytes q).take (oldLength q) = prefixBytes q := by
  rw [bytes, ← prefix_length q, List.take_left]

theorem tail_at_old_length (q : Public) : (bytes q).drop (oldLength q) = tailBytes q := by
  rw [bytes, ← prefix_length q, List.drop_left]

/-- Write offsets of the four appended writes (start offset `o`, end ≤ total).
Transfer: pool 1455..1487, domain 1487..1519, tag at 1519, no destination.
Withdrawal: pool 1427..1459, domain 1459..1491, tag at 1491, destination 1492..1524. -/
theorem tail_offsets (q : Public) :
    ((bytes q).drop (oldLength q)).take 32 = (pool q).val ∧
    ((bytes q).drop (oldLength q + 32)).take 32 = (domain q).val ∧
    ((bytes q).drop (oldLength q + 64)).take 1 = [hasDestination q] ∧
    (bytes q).drop (oldLength q + 65) = destinationBytes q ∧
    oldLength q + 65 + (destinationBytes q).length = newLength q := by
  have hp := prefix_length q
  have hd := destination_length q
  have hl := length q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tail_at_old_length, tailBytes, List.append_assoc, List.append_assoc,
      List.take_left' (raw32 _)]
  · rw [← List.drop_drop, tail_at_old_length, tailBytes, List.append_assoc, List.append_assoc,
      List.drop_left' (raw32 _), List.take_left' (raw32 _)]
  · have e : tailBytes q = ((pool q).val ++ (domain q).val) ++ ([hasDestination q] ++ destinationBytes q) := by
      simp only [tailBytes, List.append_assoc]
    have l : ((pool q).val ++ (domain q).val).length = 64 := by
      simp only [List.length_append, raw32]
    rw [← List.drop_drop, tail_at_old_length, e, List.drop_left' l]
    rfl
  · have l : ((pool q).val ++ (domain q).val ++ [hasDestination q]).length = 65 := by
      simp only [List.length_append, raw32, List.length_singleton]
    rw [← List.drop_drop, tail_at_old_length, tailBytes, List.drop_left' l]
  · cases q <;> simp only [oldLength, newLength] at hd ⊢ <;> omega

/-- Room for every appended write: each write ends at or before 1524. -/
theorem tail_room (q : Public) (pre post : List U8) (same : pre ++ post = tailBytes q) :
    (prefixBytes q ++ pre).length + post.length ≤ 1524 := by
  have hb := bound q
  rw [bytes, ← same] at hb
  simp only [List.length_append] at hb ⊢
  omega

/-- Prefix instructions keep their frozen room (`out + width ≤ 1455`), so the
frozen `prefix_room`, `words_room`, `frontier_room` (815) and `field_domain`
statements carry over verbatim when the PIN2 model is factored as
`sourceSteps` followed by the tail. -/
theorem prefix_room (q : Public) (pre rest : List Step) (s : Step) (out : List U8)
    (same : pre ++ s :: rest = sourceSteps q) (hbytes : out = pre.flatMap stepBytes) :
    out.length + (stepBytes s).length ≤ 1455 := by
  have total := prefix_length q
  have old : oldLength q ≤ 1455 := by cases q <;> simp only [oldLength] <;> omega
  rw [prefixBytes, ← same, List.flatMap_append, List.flatMap_cons, List.length_append,
    List.length_append] at total
  rw [hbytes]
  omega

/-- Init frame: 75 framing bytes plus the public bytes (1595 / 1599). -/
theorem init_frame (q : Public) :
    75 + (bytes q).length = match q with | .Transfer _ _ => 1595 | .Withdrawal _ _ => 1599 := by
  rw [length]; cases q <;> rfl

/-- Any producer whose successful output is `bytes q` returns at most 1524
bytes; this replaces `NHG_Lengths.returned` (≤ 1455) once instantiated. -/
theorem returned_of_refines {E : Type} (produce : Public → Result (core.result.Result (alloc.vec.Vec U8) E))
    (refines : ∀ q out, produce q = ok (.Ok out) → out.val = bytes q)
    (q : Public) (out : alloc.vec.Vec U8) (h : produce q = ok (.Ok out)) :
    out.val.length ≤ 1524 := by
  rw [refines q out h]; exact bound q

/-- The seed-view bound needed by `NGX_SemanticRuntime.seed_domain`
(`size ≤ 57607`) still holds with room to spare. -/
theorem seed_size_of_refines {E : Type} (produce : Public → Result (core.result.Result (alloc.vec.Vec U8) E))
    (refines : ∀ q out, produce q = ok (.Ok out) → out.val = bytes q)
    (q : Public) (out : alloc.vec.Vec U8) (h : produce q = ok (.Ok out)) :
    out.val.length ≤ 57607 := by
  have := returned_of_refines produce refines q out h; omega

/-- Teeth: the frozen length is no longer the output length. -/
theorem old_length_superseded (q : Public) : (bytes q).length ≠ oldLength q := by
  rw [length]; cases q <;> simp only [newLength, oldLength] <;> omega

#print axioms prefix_length
#print axioms tail_length
#print axioms length
#print axioms bound
#print axioms prefix_preserved
#print axioms tail_at_old_length
#print axioms tail_offsets
#print axioms tail_room
#print axioms prefix_room
#print axioms init_frame
#print axioms returned_of_refines
#print axioms seed_size_of_refines
#print axioms old_length_superseded
end AspisR1.PIN2_SerializerLengths
