import R1ReseedPrefix

/-! Advance cells are too short to decode as a strict opening-reseed frame. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedSeparation

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem parse_advance_none (p : Params M Cv L) (tag : Byte) (s : State) :
    StrictReseedDecoder.parse tag (advanceA p s) = none := by
  cases hp : StrictReseedDecoder.parse tag (advanceA p s) with
  | none => rfl
  | some c1 =>
      have hsound := StrictReseedDecoder.parse_sound tag (advanceA p s) c1 hp
      have hbytes : (advanceA p s).toBytes =
          OpeningReseedFrame.domain ++ [tag] ++ bytes c1 := hsound
      have hframe : (OpeningReseedFrame.domain ++ [tag] ++ bytes c1).length = 62 := by
        simpa [OpeningReseedFrame.frame, TrailingStateFrame.frame] using
          OpeningReseedFrame.frame_length tag c1
      have h33 : (advanceA p s).toBytes.length = 33 := by
        simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]
      rw [hbytes, hframe] at h33
      omega

theorem recover_advance_none (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (T : Table (Addr L) State)
    (hT : ∀ b v, T b = some v → v = H b ∧ Read tr b)
    (tag : Byte) (s : State)
    (hcell : T (advanceA p s) = some (H (advanceA p s))) :
    StrictReseedDecoder.recover tag T (H (advanceA p s)) = none := by
  have hfind := ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hcoll T hT
    (advanceA p s) hcell
  simp [StrictReseedDecoder.recover, hfind, parse_advance_none p tag s]

theorem decode_advance_none (p : Params M Cv L)
    (pubBytes : AspisV8R19.DuplexFrames.Bytes)
    (tag : AspisV8R19.DuplexFrames.Byte) (T : Table (Addr L) State) (fuel : Nat)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ b v, T b = some v → v = H b ∧ Read tr b)
    (s : State)
    (hcell : T (advanceA p s) = some (H (advanceA p s))) :
    ReseedPrefix.decode p pubBytes tag T fuel (H (advanceA p s)) = none := by
  simp [ReseedPrefix.decode, ReseedPrefix.raw,
    recover_advance_none p H tr Qtot hcons hQ hcoll T hT tag s hcell]

#print axioms parse_advance_none
#print axioms recover_advance_none
#print axioms decode_advance_none

end AspisR1.ReseedSeparation
end
