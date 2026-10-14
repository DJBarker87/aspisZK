import R1RawRoundDecode

/-! Decode one canonical message at its indexed record label. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.IndexedMessage

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def read (p : Params M Cv L) (i : Nat) (label : Byte) (data : Bytes) :
    Option M :=
  if label = p.lbl i then
    match p.dec data with
    | none => none
    | some m => if p.enc m = data then some m else none
  else none

theorem read_encoded (p : Params M Cv L) (i : Nat) (m : M) :
    read p i (p.lbl i) (p.enc m) = some m := by
  simp [read, p.decEnc]

theorem read_sound (p : Params M Cv L) (i : Nat) (label : Byte)
    (data : Bytes) (m : M)
    (h : read p i label data = some m) :
    label = p.lbl i ∧ p.dec data = some m ∧ p.enc m = data := by
  by_cases hl : label = p.lbl i
  · cases hd : p.dec data with
    | none => simp [read, hl, hd] at h
    | some m' =>
      by_cases he : p.enc m' = data
      · have hm : m' = m := by simpa [read, hl, hd, he] using h
        subst m'
        exact ⟨hl, rfl, he⟩
      · simp [read, hl, hd, he] at h
  · simp [read, hl] at h

theorem read_bad_label (p : Params M Cv L) (i : Nat)
    (label : Byte) (data : Bytes)
    (hlabel : label ≠ p.lbl i) :
    read p i label data = none := by
  simp [read, hlabel]

theorem read_noncanonical (p : Params M Cv L) (i : Nat)
    (label : Byte) (data : Bytes) (m : M)
    (hd : p.dec data = some m) (he : p.enc m ≠ data) :
    read p i label data = none := by
  by_cases hl : label = p.lbl i
  · simp [read, hl, hd, he]
  · simp [read, hl]

#print axioms read_encoded
#print axioms read_sound
#print axioms read_bad_label
#print axioms read_noncanonical
end AspisR1.IndexedMessage
end
