import S4SourceByteOracleV1
import S4SolanaDigestP3RegroupV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.S4P3SourceInterpretationV1
open AspisR1PublicPreparation
open AspisR1PublicPreparation.SourceDigestOracle
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisR1PublicPreparation.CallerStep
open AspisR1PublicPreparation.TranscriptStep
open AspisR1.S4SourceByteOracleV1
open S4SolanaDigestP3RegroupV1
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
attribute [local instance] Classical.propDecidable

/-- Functional interpretation under P3, with no random-oracle law asserted. -/
def hashBytes (sha256 : Bytes → Array U8 32#usize) (bs : Bytes) :=
  decodeState (sha256 bs)

theorem p3_success_interpreted {H : Type} (copyInst : core.marker.Copy H)
    (sha256 : Bytes → Array U8 32#usize) (hash : H)
    (input : Slice (Slice U8)) (out : Bytes32)
    (hd : (solanaDigestP3Model copyInst sha256).digest hash input = .ok out) :
    decodeState out = hashBytes sha256 (flatten input) := by
  have he : sha256 (flatten input) = out := Result.ok.inj hd
  simp only [hashBytes, he]

theorem p3_byteOracle_represented {H : Type} (copyInst : core.marker.Copy H)
    (sha256 : Bytes → Array U8 32#usize) (hash : H)
    (pubInput : Slice U8) (root : Bytes32) (length : U32) (bs : Bytes)
    (hex : ∃ input : Input, flatten (parts pubInput root length input) = bs) :
    byteOracle (solanaDigestP3Model copyInst sha256) hash pubInput root length bs =
      hashBytes sha256 bs := by
  unfold byteOracle
  rw [dif_pos hex]
  simp only [answer, solanaDigestP3Model, hashBytes]
  rw [Classical.choose_spec hex]

theorem p3_opening_interpreted_by_canonical_oracle {H : Type}
    (copyInst : core.marker.Copy H) (sha256 : Bytes → Array U8 32#usize)
    (hash : H) (pubInput : Slice U8) (root : Bytes32) (length : U32)
    (state : Bytes32) (tag : U8) (payload framed : Slice U8) (out : Bytes32)
    (hframe : rawBytes framed =
      (core.num.U32.to_le_bytes length).val.map decodeByte ++ rawBytes payload)
    (hd : (solanaDigestP3Model copyInst sha256).digest hash
      (openingAbsorbParts state tag length payload) = .ok out) :
    byteOracle (solanaDigestP3Model copyInst sha256) hash pubInput root length
      (flatten (openingAbsorbParts state tag length payload)) = decodeState out := by
  have hex : ∃ input : Input, flatten (parts pubInput root length input) =
      flatten (openingAbsorbParts state tag length payload) := by
    refine ⟨.absorb state tag framed, ?_⟩
    exact (opening_flatten_eq_source_absorb state tag length payload framed hframe).symm
  rw [p3_byteOracle_represented copyInst sha256 hash pubInput root length _ hex]
  exact (p3_success_interpreted copyInst sha256 hash _ out hd).symm

#print axioms p3_success_interpreted
#print axioms p3_byteOracle_represented
#print axioms p3_opening_interpreted_by_canonical_oracle
end AspisR1.S4P3SourceInterpretationV1
end
