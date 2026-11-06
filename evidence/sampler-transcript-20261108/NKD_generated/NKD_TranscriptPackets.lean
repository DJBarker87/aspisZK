import NKD_Runtime
set_option autoImplicit false
namespace AspisR1.NKD_TranscriptPackets
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
/-- Caller row bound proves the checked tag, rather than assuming a successful header. -/
theorem tag (row : U8) (bound : row.val ≤ 95) :
 ∃ t : U8, (160#u8 + row : Result U8)=ok t ∧ t.val=160+row.val := by
 obtain ⟨t,call,value⟩ := WP.spec_imp_exists
  (UScalar.add_spec (x:=160#u8) (y:=row) (by scalar_tac))
 exact ⟨t,call,value⟩
/-- Complete absorb post-state for the deployed backend; no digest reply premise. -/
theorem absorb (hashv : Slice (Slice U8) → Bytes32) (state : Bytes32)
 (row : U8) (payload : Slice U8) (bound : row.val ≤ 95) :
 ∃ t : U8, t.val=160+row.val ∧
 transcript.Transcript.absorb (NKD_Runtime.backend hashv) ⟨state,()⟩ row payload =
 ok ⟨hashv (NGT_NBA_Transcript.absorbParts state t payload),()⟩ := by
 obtain ⟨t,call,value⟩ := tag row bound
 exact ⟨t,value,NGT_NBA_Transcript.absorb _ _ row t payload _ call rfl⟩
/-- Both suffix digests are evaluated at the SAME absorbed state. Full Result,
read reply, final state, and immutable hash carrier are constructed internally. -/
theorem block (hashv : Slice (Slice U8) → Bytes32) (state : Bytes32)
 (row : U8) (payload : Slice U8) (bound : row.val ≤ 95) :
 ∃ t : U8, t.val=160+row.val ∧
 let a := hashv (NGT_NBA_Transcript.absorbParts state t payload)
 transcript.Transcript.block (NKD_Runtime.backend hashv) ⟨state,()⟩ row payload =
 ok (hashv (NGT_NBA_Transcript.readParts a 1#u8),
  ⟨hashv (NGT_NBA_Transcript.readParts a 2#u8),()⟩) := by
 obtain ⟨t,call,value⟩ := tag row bound
 exact ⟨t,value,NGT_NBA_Transcript.block _ _ row t payload _ _ _ call rfl rfl rfl⟩
/-- All deployed variants: exact domain29/tag1/semantic32 and SAME hash carrier. -/
theorem new (hashv : Slice (Slice U8) → Bytes32) (semantic : Bytes32)
 (variant : transport.Variant) :
 transcript.Transcript.new (NKD_Runtime.backend hashv) () semantic variant =
 (do let t ← transport.Variant.tag variant
     ok (⟨hashv (NKD_New.parts semantic t),()⟩ : transcript.Transcript Unit)) := by
 rw [NKD_Runtime.new_root]
 unfold NKD_New.G NKD_Runtime.backend NGT_BlockAssociation.runtime NGC_DigestRef.digest_ref
 rfl
#print axioms tag
#print axioms absorb
#print axioms block
#print axioms new
#check @absorb
#check @block
#check @new
end AspisR1.NKD_TranscriptPackets
