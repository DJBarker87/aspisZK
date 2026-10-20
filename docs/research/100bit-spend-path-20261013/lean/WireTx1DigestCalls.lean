import WireTx1PrefixRecords
import ExtractedDigest32Begin

/-! Typed inputs of retained validated semantic/circle steps. Exact dictionary
calls are retained; this is not an instrumented deployed tx1 trace theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.WireTx1
open r1_wire TranscriptStep

def inputBytes (parts : Slice (Slice U8)) : List U8 :=
  parts.val.flatMap (fun part => part.val)

inductive TypedStepInput : Slice (Slice U8) → Prop where
  | absorb (state : Bytes32) (row tag : U8) (frame payload : Slice U8)
      (htag : tag.val = 160 + row.val)
      (framing : AspisR1.ExtractedRecordFraming.SuccessfulFraming row frame payload) :
      TypedStepInput (absorbParts state tag frame)
  | read (state : Bytes32) (tag : U8) (htag : tag = 1#u8 ∨ tag = 2#u8) :
      TypedStepInput (readParts state tag)

theorem absorb_length (state : Bytes32) (tag : U8) (frame : Slice U8) :
    (inputBytes (absorbParts state tag frame)).length = 34 + frame.val.length := by
  have hs : state.val.length = 32 := state.property
  simp [inputBytes, absorbParts, Array.to_slice, Array.make, hs]
  omega

theorem read_length (state : Bytes32) (tag : U8) :
    (inputBytes (readParts state tag)).length = 33 := by
  have hs : state.val.length = 32 := state.property
  simp [inputBytes, readParts, Array.to_slice, Array.make, hs]

theorem typed_step_lengths (parts : Slice (Slice U8)) (h : TypedStepInput parts) :
    (inputBytes parts).length = 39 ∨ (inputBytes parts).length = 71 ∨
    (inputBytes parts).length = 935 ∨ (inputBytes parts).length = 3751 ∨
    (inputBytes parts).length = 967 ∨ (inputBytes parts).length = 33 := by
  cases h with
  | read state tag ht => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (read_length state tag)))))
  | absorb state row tag frame payload ht hf =>
    rw [absorb_length]
    obtain ⟨payloadTag, size, b1, b2, b3, b4, htable, hlen, rest⟩ := hf
    have hs : size.val = 0 ∨ size.val = 32 ∨ size.val = 896 ∨
        size.val = 3712 ∨ size.val = 928 := by
      unfold AspisR1.ExtractedRowShape.table at htable
      split_ifs at htable <;> simp at htable
      all_goals rcases htable with ⟨_, rfl⟩ <;> norm_num
    omega

/-- The input's exact payload tag and LE32 length follow from parser success.
The outer duplex label is fixed independently by checked addition. -/
theorem validated_step_typed {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (row : U8) (record : ValidatedRecord)
    (ha : Prefix.validated_record pre row = ok (.Ok record)) (hadmit : row.val ≤ 26)
    (self after : SemanticTranscript H) (block : Bytes32)
    (h : SemanticTranscript.sample_block_validated D self record.row record.framed =
      ok (.Ok block, after)) :
    ∃ tag next absorbed state,
      D.digest self.hash (absorbParts self.state tag record.framed) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      TypedStepInput (absorbParts self.state tag record.framed) ∧
      TypedStepInput (readParts absorbed 1#u8) ∧
      TypedStepInput (readParts absorbed 2#u8) ∧
      tag.val = 160 + row.val ∧ after = { self with state, next_row := next } := by
  obtain ⟨hr, payload, hf⟩ := accessor_framing bytes pre hp row record ha
  obtain ⟨_, tag, next, absorbed, state, ht, _, hab, hb, hs, he⟩ :=
    step_success D self after record.row record.framed block (by rw [hr]; exact hadmit) h
  have ht' : tag.val = 160 + row.val := by simpa only [hr] using ht
  exact ⟨tag, next, absorbed, state, hab, hb, hs,
    .absorb self.state row tag record.framed payload ht' hf,
    .read absorbed 1#u8 (Or.inl rfl), .read absorbed 2#u8 (Or.inr rfl), ht', he⟩

inductive TypedSemanticRun {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix) :
    List U8 → SemanticTranscript H → SemanticTranscript H → List aspis_core.field.QM31 → Prop
  | nil (self) : TypedSemanticRun D pre [] self self []
  | cons {row rows self mid after q qs record block tag absorbed state}
      (accessor : Prefix.validated_record pre row = ok (.Ok record))
      (call : SemanticTranscript.semantic_validated D self record = ok (.Ok q, mid))
      (absorbCall : D.digest self.hash (absorbParts self.state tag record.framed) = ok absorbed)
      (blockCall : D.digest self.hash (readParts absorbed 1#u8) = ok block)
      (advanceCall : D.digest self.hash (readParts absorbed 2#u8) = ok state)
      (typed : TypedStepInput (absorbParts self.state tag record.framed))
      (tail : TypedSemanticRun D pre rows mid after qs) :
      TypedSemanticRun D pre (row :: rows) self after (q :: qs)

theorem run_typed {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    {rows self after qs} (run : BeginCalls.SemanticRun D pre rows self after qs) :
    TypedSemanticRun D pre rows self after qs := by
  induction run with
  | nil => exact .nil _
  | @cons row rows self mid after q qs record ha hs tail ih =>
    obtain ⟨hbound, block, hb, _⟩ := CallerStep.semantic_success D self mid record q hs
    have hr := (accessor_bytes pre row record ha).1
    obtain ⟨tag, next, absorbed, state, hab, hbl, hadv, ht, _⟩ :=
      validated_step_typed D bytes pre hp row record ha (by rw [← hr]; omega) self mid block hb
    exact .cons ha hs hab hbl hadv ht ih

/-- All 45 digest calls of the fifteen-row retained `begin` use typed input
classes; no per-call parser or byte identity hypothesis is supplied. Read
inputs are the fixed `readParts state 1/2` constructors, each 33 bytes. -/
theorem begin_typed {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (self after : SemanticTranscript H) (out : Challenges)
    (h : begin D pre self = ok (.Ok out, after)) :
    TypedSemanticRun D pre BeginCalls.rows self after (BeginCalls.challengeList out) := by
  obtain ⟨qs, run, he⟩ := BeginCalls.begin_success D pre self after out h
  simpa only [he] using run_typed D bytes pre hp run

/-- A necessary size condition for the requested transcript/leaf/node/root
classes. Checkpoint proof binding is outside this envelope. -/
def ListedClassSize (n : Nat) : Prop := n ≤ 3751

theorem compact_proof_outside_listed_classes (proof : Slice U8)
    (hlen : proof.val.length = 57607) : ¬ ListedClassSize proof.val.length := by
  unfold ListedClassSize
  omega

#print axioms absorb_length
#print axioms read_length
#print axioms typed_step_lengths
#print axioms validated_step_typed
#print axioms run_typed
#print axioms begin_typed
#print axioms compact_proof_outside_listed_classes
end AspisR1PublicPreparation.WireTx1
