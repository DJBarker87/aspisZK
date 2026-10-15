import R1RawRoundDecode

/-! Successful raw decoding is reversible when decoding is canonical. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRoundCanonical

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}

/-- If every successful decode re-encodes to its original bytes, then a
successful list decode preserves the entire raw record list. -/
theorem encode_of_decode (p : Params M Cv L)
    (hcanonical : ∀ data m, p.dec data = some m → p.enc m = data)
    (j : Nat) (raw : List RawRec) (out : List (Rec M))
    (h : RawRoundDecode.decode p j raw = some out) :
    RawRoundDecode.encode p j out = raw := by
  induction raw generalizing j out with
  | nil =>
      simp [RawRoundDecode.decode] at h
      subst out
      rfl
  | cons q raw ih =>
      cases q with
      | mk prev absorbed label data next =>
        by_cases hl : label = p.lbl j
        · cases hd : p.dec data with
          | none => simp [RawRoundDecode.decode, hl, hd] at h
          | some m =>
            cases ht : RawRoundDecode.decode p (j + 1) raw with
            | none => simp [RawRoundDecode.decode, hl, hd, ht] at h
            | some tail =>
                have hout : (prev, absorbed, m, next) :: tail = out := by
                  simpa [RawRoundDecode.decode, hl, hd, ht] using h
                have htail := ih (j + 1) tail ht
                have hbytes := hcanonical data m hd
                cases hout
                simp [RawRoundDecode.encode, RawRoundDecode.rawOf,
                  hl, hbytes, htail]
        · simp [RawRoundDecode.decode, hl] at h

#print axioms encode_of_decode

end AspisR1.RawRoundCanonical
end
