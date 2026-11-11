import R1SemanticPublicWireRoundTrip
import R1SemanticPublicWireSound
import R1SemanticPublicWireInjective

/-! Model-level binding of the complete section-9 semantic public bytes.
This does not identify an ASF8 decoder or the Rust serializer with the model.
PIN2 (2026-11-10): the bytes include the pool/domain/destination suffix. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicByteBinding
open SemanticPublicWire

theorem parsed_wire (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) :
    ∃ wire, decode bytes = some wire ∧ toPublic wire = pub := by
  cases hd : decode bytes with
  | none => simp [parsePublic, hd] at h
  | some wire =>
      simp only [parsePublic, hd] at h
      change (if PublicOptionShape.check (toPublic wire) = true
        then some (toPublic wire) else none) = some pub at h
      split at h
      next hc => exact ⟨wire, rfl, Option.some.inj h⟩
      next hc => contradiction

theorem parsed_index_bound (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) : pub.nextPairIndex < 2^64 := by
  obtain ⟨wire, _, hw⟩ := parsed_wire bytes pub h
  rw [← hw]
  exact toPublic_index_bound wire

theorem parsed_exact_bytes (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) :
    ∃ wire, toPublic wire = pub ∧ encode wire = bytes := by
  obtain ⟨wire, hd, hw⟩ := parsed_wire bytes pub h
  exact ⟨wire, hw, SemanticPublicWireSound.encode_of_decode bytes wire hd⟩

theorem bytes_unique (left right : List Byte) (pub : R0P.Public M31)
    (hl : parsePublic left = some pub) (hr : parsePublic right = some pub) :
    left = right := by
  obtain ⟨wl, hpl, hel⟩ := parsed_exact_bytes left pub hl
  obtain ⟨wr, hpr, her⟩ := parsed_exact_bytes right pub hr
  have hw : wl = wr := SemanticPublicWireInjective.toPublic_injective (hpl.trans hpr.symm)
  exact hel.symm.trans ((congrArg encode hw).trans her)

/-- PIN2: 1520 bytes for a transfer, 1524 for a withdrawal (was 1455/1427). -/
theorem parsed_length (bytes : List Byte) (pub : R0P.Public M31)
    (h : parsePublic bytes = some pub) :
    bytes.length = if pub.variant = .privateTransfer then 1520 else 1524 := by
  obtain ⟨wire, hp, he⟩ := parsed_exact_bytes bytes pub h
  have hc : PublicOptionShape.canonical (toPublic wire) := hp ▸ parsePublic_canonical bytes pub h
  rw [← he, ← hp, SemanticPublicWireRoundTrip.encode_length_canonical wire hc]
  cases wire <;> simp [toPublic]

#print axioms parsed_wire
#print axioms parsed_index_bound
#print axioms parsed_exact_bytes
#print axioms bytes_unique
#print axioms parsed_length
end AspisR1.SemanticPublicByteBinding
