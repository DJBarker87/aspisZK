import RawPublicInitRecovery
import R1PublicInitAbsorbSeparation

/-! Strict initial-frame parsing that recovers its public statement from the
input itself. Ordinary absorb frames are rejected for every candidate public. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicInitParser
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def parse {L : Nat} (a : Addr L) : Option (UnifiedSampler.Public L × State) :=
  (RawPublicInitRecovery.recover L a.toBytes).bind fun pub =>
    (PublicInitParse.parse pub.pubBytes a).map fun root => (pub,root)

theorem of_fixed_parse {L : Nat} (pub : UnifiedSampler.Public L)
    (a : Addr L) (root : State) (htag : pub.tag = 2)
    (hp : PublicInitParse.parse pub.pubBytes a = some root) : parse a = some (pub,root) := by
  unfold parse
  rw [RawPublicInitRecovery.recover_of_parse pub a root htag hp]
  simp only [Option.bind_some,hp,Option.map_some]

theorem parse_sound {L : Nat} (a : Addr L) (pub : UnifiedSampler.Public L) (root : State)
    (hp : parse a = some (pub,root)) :
    RawPublicInitRecovery.recover L a.toBytes = some pub ∧
      PublicInitParse.parse pub.pubBytes a = some root := by
  unfold parse at hp
  cases hr : RawPublicInitRecovery.recover L a.toBytes with
  | none => simp [hr] at hp
  | some p =>
      simp only [hr,Option.bind_some] at hp
      cases hs : PublicInitParse.parse p.pubBytes a with
      | none => simp [hs] at hp
      | some r =>
          simp only [hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hp
          rcases hp with ⟨rfl,rfl⟩
          exact ⟨rfl,hs⟩

theorem parse_absorb_none {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (s : State) (label : Byte) (data : Bytes) (hdata : data.length ≤ p.D) :
    parse (absorbA p s label data hdata) = none := by
  unfold parse
  cases hr : RawPublicInitRecovery.recover L (absorbA p s label data hdata).toBytes with
  | none => rfl
  | some pub =>
      simp only [Option.bind_some]
      rw [PublicInitAbsorbSeparation.parse_init_absorb_none p pub.pubBytes s label data hdata]
      rfl

#print axioms of_fixed_parse
#print axioms parse_sound
#print axioms parse_absorb_none
end AspisR1.RawPublicInitParser
end
