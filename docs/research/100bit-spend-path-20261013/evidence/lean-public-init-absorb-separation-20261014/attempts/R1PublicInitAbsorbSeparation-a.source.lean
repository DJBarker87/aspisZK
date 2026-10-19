import R1PublicInitParse

/-! Deterministic separation of the P3 initialization prefix from absorb frames.
This is a byte-framing fact; it does not assert source correspondence. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PublicInitAbsorbSeparation

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem parseAbsorb_none_of_init {L : Nat} (pubBytes : Bytes) (a : Addr L)
    (c1 : State) (h : PublicInitParse.parse pubBytes a = some c1) :
    parseAbsorb a = none := by
  have hs := PublicInitParse.parse_sound pubBytes a c1 h
  have htag : a.toBytes.getD 32 (1 : Byte) = 84 := by
    rw [hs.2]
    simp [PublicInitFrame.domain, PublicInitFrame.lengthBytes]
  unfold parseAbsorb
  rw [if_neg]
  · rfl
  · intro hcond
    exact (by norm_num : (84 : Byte) ≠ 0) (by simpa [htag] using hcond.2)

theorem parse_init_absorb_none {M Cv : Type} {L : Nat}
    (p : Params M Cv L) (pubBytes : Bytes) (s : State) (label : Byte)
    (data : Bytes) (hdata : data.length ≤ p.D) :
    PublicInitParse.parse pubBytes (absorbA p s label data hdata) = none := by
  cases hparse : PublicInitParse.parse pubBytes (absorbA p s label data hdata) with
  | none => rfl
  | some c1 =>
      have hnone := parseAbsorb_none_of_init pubBytes
        (absorbA p s label data hdata) c1 hparse
      rw [parseAbsorb_absorbA] at hnone
      exact False.elim (Option.noConfusion hnone)

#print axioms parseAbsorb_none_of_init
#print axioms parse_init_absorb_none

end AspisR1.PublicInitAbsorbSeparation
end
