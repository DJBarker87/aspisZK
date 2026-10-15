import R1SelectedTranscriptParams
import R1RawRoundCanonical

/-! Canonicality and successful raw-record round trips for the selected
bounded message codec. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedRawCanonical

open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

/-- A successful bounded decode re-encodes to the original byte list. -/
theorem dec_sound (bs : Bytes) (m : SelectedTranscriptParams.Message)
    (h : SelectedTranscriptParams.dec bs = some m) :
    SelectedTranscriptParams.enc m = bs := by
  unfold SelectedTranscriptParams.dec at h
  by_cases hb : bs.length ≤ SelectedTranscriptParams.D
  · simp [hb] at h
    cases h
    rfl
  · simp [hb] at h

/-- Every successfully decoded raw record sequence is reproduced exactly
by the selected codec's encoder. -/
theorem encode_of_decode (j : Nat) (raw : List RawRec)
    (out : List (FS2.Duplex.Rec SelectedTranscriptParams.Message))
    (h : RawRoundDecode.decode SelectedTranscriptParams.params j raw = some out) :
    RawRoundDecode.encode SelectedTranscriptParams.params j out = raw := by
  apply AspisR1.RawRoundCanonical.encode_of_decode
    SelectedTranscriptParams.params
    (fun data m hm => dec_sound data m hm)
    j raw out h

#print axioms dec_sound
#print axioms encode_of_decode

end AspisR1.SelectedRawCanonical
end
