import R1InitialWalk

/-! A record-list codec for the abstract duplex decoder records. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRoundDecode

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}

def rawOf (p : Params M Cv L) (j : Nat) (r : Rec M) : RawRec :=
  ⟨r.1, r.2.1, p.lbl j, p.enc r.2.2.1, r.2.2.2⟩

def encode (p : Params M Cv L) : Nat → List (Rec M) → List RawRec
  | _, [] => []
  | j, r :: rs => rawOf p j r :: encode p (j + 1) rs

def decode (p : Params M Cv L) : Nat → List RawRec → Option (List (Rec M))
  | _, [] => some []
  | j, r :: rs =>
      if r.label = p.lbl j then
        match p.dec r.data with
        | none => none
        | some m =>
            (decode p (j + 1) rs).map
              (fun out => (r.prev, r.absorbed, m, r.next) :: out)
      else none

theorem decode_encode (p : Params M Cv L) (j : Nat) (rs : List (Rec M)) :
    decode p j (encode p j rs) = some rs := by
  induction rs generalizing j with
  | nil => simp [encode, decode]
  | cons r rs ih =>
      simp [encode, decode, rawOf, p.decEnc, ih]

theorem encode_length (p : Params M Cv L) :
    ∀ (j : Nat) (rs : List (Rec M)), (encode p j rs).length = rs.length := by
  intro j rs
  induction rs generalizing j with
  | nil => rfl
  | cons r rs ih => simp [encode, ih]

theorem decode_length (p : Params M Cv L) :
    ∀ (j : Nat) (raw : List RawRec) (out : List (Rec M)),
      decode p j raw = some out → out.length = raw.length := by
  intro j raw
  induction raw generalizing j with
  | nil =>
      intro out h
      simp [decode] at h
      subst out
      rfl
  | cons q raw ih =>
      cases q with
      | mk prev absorbed label data next =>
        intro out h
        by_cases hl : label = p.lbl j
        · cases hd : p.dec data with
          | none => simp [decode, hl, hd] at h
          | some m =>
            cases hr : decode p (j + 1) raw with
            | none => simp [decode, hl, hd, hr] at h
            | some decoded =>
              have hout : (prev, absorbed, m, next) :: decoded = out := by
                simpa [decode, hl, hd, hr] using h
              cases hout
              simp only [List.length_cons]
              have hrec := ih (j + 1) decoded hr
              omega
        · simp only [decode, if_neg hl] at h
          cases h

theorem decode_append_one (p : Params M Cv L) (j : Nat)
    (rs : List RawRec) (out : List (Rec M)) (r : Rec M)
    (h : decode p j rs = some out) :
    decode p j (rs ++ [rawOf p (j + rs.length) r]) = some (out ++ [r]) := by
  induction rs generalizing j out with
  | nil =>
      have hout : out = [] := by simpa [decode] using h
      subst out
      simp [decode, rawOf, p.decEnc]
  | cons q rs ih =>
      cases q with
      | mk prev absorbed label data next =>
        by_cases hl : label = p.lbl j
        · cases hd : p.dec data with
          | none => simp [decode, hl, hd] at h
          | some m =>
            cases htail : decode p (j + 1) rs with
            | none => simp [decode, hl, hd, htail] at h
            | some outTail =>
              have hout : (prev, absorbed, m, next) :: outTail = out := by
                simpa [decode, hl, hd, htail] using h
              cases hout
              have ih' := ih (j + 1) outTail htail
              simp only [List.cons_append, decode, if_pos hl, hd]
              rw [show j + (RawRec.mk prev absorbed label data next :: rs).length =
                j + 1 + rs.length by simp [Nat.add_assoc]; omega]
              rw [ih']
              rfl
        · simp only [decode, if_neg hl] at h
          cases h

#print axioms decode_encode
#print axioms encode_length
#print axioms decode_length
#print axioms decode_append_one

end AspisR1.RawRoundDecode
end
