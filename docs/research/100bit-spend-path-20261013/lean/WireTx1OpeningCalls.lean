import WireTx1DigestCalls

/-! Retained opening duplex facts. The row-width premise is the named boundary
to optimized Prepared::new / compact expansion, not a tx1-success theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.WireTx1
open r1_wire TranscriptStep CallerStep

def openingSize : Nat → Option Nat
  | 27 => some 928 | 28 => some 32 | 29 => some 224
  | 30 => some 256 | 31 => some 2048 | 32 => some 0 | _ => none

def OpeningPayload (row : U8) (payload : Slice U8) : Prop :=
  openingSize row.val = some payload.val.length

inductive TypedOpeningInput : Slice (Slice U8) → Prop where
  | reseed (semantic : Bytes32) (variant : transport.Variant) :
      TypedOpeningInput (reseedParts semantic variant)
  | absorb (state : Bytes32) (row tag : U8) (payload : Slice U8)
      (width : OpeningPayload row payload) (htag : tag.val = 160 + row.val) :
      TypedOpeningInput (openingAbsorbParts state tag
        (UScalar.cast .U32 (Slice.len payload)) payload)

theorem opening_payload_bound (row : U8) (payload : Slice U8)
    (h : OpeningPayload row payload) : row.val ≤ 32 := by
  unfold OpeningPayload openingSize at h
  split at h <;> simp_all <;> omega

theorem opening_absorb_length (state : Bytes32) (tag : U8) (length : U32)
    (payload : Slice U8) :
    (inputBytes (openingAbsorbParts state tag length payload)).length =
      38 + payload.val.length := by
  have hs : state.val.length = 32 := state.property
  have hl : (core.num.U32.to_le_bytes length).val.length = 4 :=
    (core.num.U32.to_le_bytes length).property
  simp [inputBytes, openingAbsorbParts, Array.to_slice, Array.make, hs, hl]
  omega

theorem reseed_length (semantic : Bytes32) (variant : transport.Variant) :
    (inputBytes (reseedParts semantic variant)).length = 62 := by
  have hs : semantic.val.length = 32 := semantic.property
  simp [inputBytes, reseedParts, openingDomain, Array.to_slice, Array.make, hs]

/-- Actual constructor equation, with its sole digest input classified. -/
theorem opening_new_typed {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (semantic : Bytes32) (variant : transport.Variant) :
    transcript.Transcript.new D hash semantic variant =
      (do let state ← D.digest hash (reseedParts semantic variant); ok { state, hash }) ∧
      TypedOpeningInput (reseedParts semantic variant) :=
  ⟨opening_new_eq D hash semantic variant, .reseed semantic variant⟩

/-- Success of the retained block fixes all three inputs. The width premise
must still be supplied by the deployed opening caller. -/
theorem opening_block_typed {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (width : OpeningPayload row payload) (block : Bytes32)
    (h : transcript.Transcript.block D self row payload = ok (block, after)) :
    ∃ tag absorbed state,
      D.digest self.hash (openingAbsorbParts self.state tag
        (UScalar.cast .U32 (Slice.len payload)) payload) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      TypedOpeningInput (openingAbsorbParts self.state tag
        (UScalar.cast .U32 (Slice.len payload)) payload) ∧
      TypedStepInput (readParts absorbed 1#u8) ∧
      TypedStepInput (readParts absorbed 2#u8) ∧ after = { self with state } := by
  have hr := opening_payload_bound row payload width
  obtain ⟨tag, ht, htv⟩ := WP.spec_imp_exists
    (U8.add_spec (x := 160#u8) (y := row) (by scalar_tac))
  obtain ⟨mid, state, ha, hb, hs, he⟩ := opening_block_success D self after row payload block h
  rw [opening_absorb_eq D self row tag payload _ ht rfl] at ha
  obtain ⟨absorbed, hab, hout⟩ := bind_success _ _ _ ha
  have hm : mid = { self with state := absorbed } := (Result.ok.inj hout).symm
  subst mid
  exact ⟨tag, absorbed, state, hab, hb, hs,
    .absorb self.state row tag payload width (by simpa using htv),
    .read absorbed 1#u8 (Or.inl rfl), .read absorbed 2#u8 (Or.inr rfl), he⟩
#print axioms opening_payload_bound
#print axioms opening_absorb_length
#print axioms reseed_length
#print axioms opening_new_typed
#print axioms opening_block_typed
end AspisR1PublicPreparation.WireTx1
