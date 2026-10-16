import R1PublicInitParse
import R1UnifiedSampler

/-! Recover the public bytes from an initial hash input without being given
the public statement. The fixed tag is the selected source tag 2. This is a
candidate constructor; existing strict initial parsing supplies authenticity. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicInitRecovery
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def publicBytes (a : Bytes) : Bytes := (a.drop 43).take (a.length - 75)

theorem publicBytes_frame (pub : Bytes) (root : State) :
    publicBytes (PublicInitFrame.frame pub root) = pub := by
  have hhead : (PublicInitFrame.domain ++ [0] ++ PublicInitFrame.lengthBytes pub.length).length = 43 := by
    simp only [List.length_append,List.length_singleton,PublicInitFrame.lengthBytes_length]
    rfl
  have hdrop : (PublicInitFrame.frame pub root).drop 43 = pub ++ bytes root := by
    change ((PublicInitFrame.domain ++ [0] ++ PublicInitFrame.lengthBytes pub.length) ++ pub ++ bytes root).drop 43 = _
    rw [List.append_assoc,← hhead]
    simp
  unfold publicBytes
  rw [PublicInitFrame.frame_length,hdrop]
  have hn : 75 + pub.length - 75 = pub.length := by omega
  rw [hn]
  simp

def recover (L : Nat) (a : Bytes) : Option (UnifiedSampler.Public L) :=
  if h : 75 + (publicBytes a).length ≤ L then some ⟨publicBytes a,h,2⟩ else none

theorem recover_frame {L : Nat} (pub : UnifiedSampler.Public L) (root : State)
    (htag : pub.tag = 2) :
    recover L (PublicInitFrame.frame pub.pubBytes root) = some pub := by
  unfold recover
  rw [publicBytes_frame]
  split
  · apply congrArg some
    cases pub with
    | mk b h t => simp_all
  · rename_i hnot
    exact (hnot pub.initFits).elim

theorem recover_of_parse {L : Nat} (pub : UnifiedSampler.Public L)
    (a : Addr L) (root : State) (htag : pub.tag = 2)
    (hp : PublicInitParse.parse pub.pubBytes a = some root) :
    recover L a.toBytes = some pub := by
  have ha : a.toBytes = PublicInitFrame.frame pub.pubBytes root :=
    (PublicInitParse.parse_sound pub.pubBytes a root hp).2
  rw [ha]
  exact recover_frame pub root htag

#print axioms publicBytes_frame
#print axioms recover_frame
#print axioms recover_of_parse
end AspisR1.RawPublicInitRecovery
end
