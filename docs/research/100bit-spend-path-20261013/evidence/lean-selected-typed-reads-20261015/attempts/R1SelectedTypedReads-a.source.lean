import R1SelectedRawCanonical
import R1RawRoundEncodeAppend
import R1SelectedSemanticRead
import R1SelectedOpeningRead
import R1SelectedTranscriptRead

/-! Compose the selected raw payload readers with the canonical encoder for
already typed duplex records. This remains a representation/list-model result;
it does not establish that a Rust transcript or accepted run has these records.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedTypedReads

open AspisR1.InitialWalk
open FS2.Duplex

abbrev Record := Rec SelectedTranscriptParams.Message

def semantic (rs : List Record) : Option SelectedSemanticRead.Payloads :=
  SelectedSemanticRead.read (RawRoundDecode.encode SelectedTranscriptParams.params 0 rs)

def opening (rs : List Record) : Option SelectedOpeningData.Payloads :=
  SelectedOpeningRead.read (RawRoundDecode.encode SelectedTranscriptParams.params 0 rs)

def transcript (rs : List Record) : Option SelectedTranscriptRead.Payloads :=
  SelectedTranscriptRead.read (RawRoundDecode.encode SelectedTranscriptParams.params 0 rs)

theorem semantic_eq_raw_of_decode (raw : List RawRec) (rs : List Record)
    (hdecode : RawRoundDecode.decode SelectedTranscriptParams.params 0 raw = some rs) :
    semantic rs = SelectedSemanticRead.read raw := by
  unfold semantic
  rw [SelectedRawCanonical.encode_of_decode 0 raw rs hdecode]

theorem opening_eq_raw_of_decode (raw : List RawRec) (rs : List Record)
    (hdecode : RawRoundDecode.decode SelectedTranscriptParams.params 0 raw = some rs) :
    opening rs = SelectedOpeningRead.read raw := by
  unfold opening
  rw [SelectedRawCanonical.encode_of_decode 0 raw rs hdecode]

theorem transcript_eq_raw_of_decode (raw : List RawRec) (rs : List Record)
    (hdecode : RawRoundDecode.decode SelectedTranscriptParams.params 0 raw = some rs) :
    transcript rs = SelectedTranscriptRead.read raw := by
  unfold transcript
  rw [SelectedRawCanonical.encode_of_decode 0 raw rs hdecode]

theorem semantic_append_stable (rs tail : List Record)
    (h : 24 < rs.length) : semantic (rs ++ tail) = semantic rs := by
  unfold semantic
  rw [RawRoundEncodeAppend.encode_append]
  simp only [Nat.zero_add]
  apply SelectedSemanticRead.read_append_stable
  rw [RawRoundDecode.encode_length]
  exact h

theorem opening_append_stable (rs tail : List Record)
    (h : 31 < rs.length) : opening (rs ++ tail) = opening rs := by
  unfold opening
  rw [RawRoundEncodeAppend.encode_append]
  simp only [Nat.zero_add]
  apply SelectedOpeningRead.read_append_stable
  rw [RawRoundDecode.encode_length]
  exact h

theorem transcript_append_stable (rs tail : List Record)
    (h : 32 < rs.length) : transcript (rs ++ tail) = transcript rs := by
  unfold transcript
  rw [RawRoundEncodeAppend.encode_append]
  simp only [Nat.zero_add]
  apply SelectedTranscriptRead.read_append_stable
  rw [RawRoundDecode.encode_length]
  exact h

#print axioms semantic_eq_raw_of_decode
#print axioms opening_eq_raw_of_decode
#print axioms transcript_eq_raw_of_decode
#print axioms semantic_append_stable
#print axioms opening_append_stable
#print axioms transcript_append_stable

end AspisR1.SelectedTypedReads
end
