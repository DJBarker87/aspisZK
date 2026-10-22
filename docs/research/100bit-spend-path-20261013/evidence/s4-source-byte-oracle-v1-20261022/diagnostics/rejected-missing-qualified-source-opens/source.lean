import ExtractedSourceDigestOracle
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.S4SourceByteOracleV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.SourceDigestOracle
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep FS2.Duplex
attribute [local instance] Classical.propDecidable

/-- Byte-addressed presentation of the existing source-derived functional
oracle. This constructs no new distribution or freshness guarantee. -/
def byteOracle {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (bs : Bytes) : State :=
  if h : ∃ input : Input, flatten (parts pubInput root length input) = bs then
    answer D hash (parts pubInput root length (Classical.choose h))
  else 0

theorem byteOracle_address {Hash : Type} {L : Nat}
    (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (a : Addr L) :
    byteOracle D hash pubInput root length a.toBytes =
      SourceDigestOracle.oracle D hash pubInput root length a := by rfl

theorem byteOracle_source_call {Hash : Type}
    (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (input : Input) (out : TranscriptStep.Bytes32)
    (hd : D.digest hash (parts pubInput root length input) = .ok out) :
    byteOracle D hash pubInput root length (flatten (parts pubInput root length input)) =
      decodeState out := by
  have hex : ∃ i : Input, flatten (parts pubInput root length i) =
      flatten (parts pubInput root length input) := ⟨input,rfl⟩
  have hchosen := Classical.choose_spec hex
  have he := parts_of_flat pubInput root length (Classical.choose hex) input hchosen
  unfold byteOracle
  rw [dif_pos hex, he]
  simp only [answer, hd]
#print axioms byteOracle_address
#print axioms byteOracle_source_call
end AspisR1.S4SourceByteOracleV1
end
