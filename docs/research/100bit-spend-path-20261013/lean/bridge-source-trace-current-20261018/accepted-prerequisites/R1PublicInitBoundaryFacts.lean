import R1PublicInitParse

/-! Public initialization frames are length-separated from state-only frames. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PublicInitBoundaryFacts

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem parse_squeeze_none (p : Params M Cv L) (pubBytes : Bytes) (s : State) :
    PublicInitParse.parse pubBytes (squeezeA p s) = none := by
  cases hp : PublicInitParse.parse pubBytes (squeezeA p s) with
  | none => rfl
  | some c1 =>
      have hsound := PublicInitParse.parse_sound pubBytes (squeezeA p s) c1 hp
      have hbytes : (squeezeA p s).toBytes =
          PublicInitFrame.pre pubBytes ++ bytes c1 := by
        simpa [PublicInitFrame.pre] using hsound.2
      have hframe : (PublicInitFrame.pre pubBytes ++ bytes c1).length =
          75 + pubBytes.length := by
        rw [List.length_append, PublicInitFrame.pre_length, bytes_length]
        omega
      have h33 : (squeezeA p s).toBytes.length = 33 := by
        simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
      rw [hbytes, hframe] at h33
      omega

theorem parse_advance_none (p : Params M Cv L) (pubBytes : Bytes) (s : State) :
    PublicInitParse.parse pubBytes (advanceA p s) = none := by
  cases hp : PublicInitParse.parse pubBytes (advanceA p s) with
  | none => rfl
  | some c1 =>
      have hsound := PublicInitParse.parse_sound pubBytes (advanceA p s) c1 hp
      have hbytes : (advanceA p s).toBytes =
          PublicInitFrame.pre pubBytes ++ bytes c1 := by
        simpa [PublicInitFrame.pre] using hsound.2
      have hframe : (PublicInitFrame.pre pubBytes ++ bytes c1).length =
          75 + pubBytes.length := by
        rw [List.length_append, PublicInitFrame.pre_length, bytes_length]
        omega
      have h33 : (advanceA p s).toBytes.length = 33 := by
        simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]
      rw [hbytes, hframe] at h33
      omega

#print axioms parse_squeeze_none
#print axioms parse_advance_none

end AspisR1.PublicInitBoundaryFacts
end
