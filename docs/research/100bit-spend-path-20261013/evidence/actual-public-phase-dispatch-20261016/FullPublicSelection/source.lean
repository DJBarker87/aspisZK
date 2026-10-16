import EarlyPublicTotalCase
import RawPublicOpeningWalk
import RawLatePublicSelector
import R1UnifiedLabels

/-! Dispatch a public-free selector by the actual absorbed round label.
Early semantic, opening and post-query recovery are separate branches, so no
unproved uniqueness across successful competing selectors is needed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FullPublicSelection
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def select (p : Params M Cv L) (a : Addr L) (T : Table (Addr L) State) :
    Option (UnifiedSampler.Public L) :=
  match parseAbsorb a with
  | none => EarlyPublicSelection.initial a
  | some (endpoint, label, _) =>
      if UnifiedLabels.row label ≤ 26 then SemanticPublicSelection.select p T endpoint
      else if UnifiedLabels.row label ≤ 31 then RawPublicOpeningWalk.select p T 2 4 endpoint
      else RawLatePublicSelector.select p T 2 4 a

theorem initial (p : Params M Cv L) (pub : UnifiedSampler.Public L) (root : State)
    (hlen : pub.pubBytes.length < 2^32) (htag : pub.tag = 2) (T : Table (Addr L) State) :
    select p (PublicInitFrame.addr pub.pubBytes pub.initFits root) T = some pub := by
  have hp := PublicInitParse.parse_addr pub.pubBytes hlen pub.initFits root
  have hn := PublicInitAbsorbSeparation.parseAbsorb_none_of_init pub.pubBytes _ root hp
  simp only [select,hn]
  exact EarlyPublicSelection.initial_addr pub root hlen htag

theorem early (p : Params M Cv L) (T : Table (Addr L) State)
    (s : State) (data : Bytes) (hdata : data.length ≤ p.D)
    (n : Nat) (hn : n ≤ 26) (hl : p.lbl n = UnifiedLabels.label n) :
    select p (absorbA p s (p.lbl n) data hdata) T =
      EarlyPublicSelection.ordinary p (absorbA p s (p.lbl n) data hdata) T := by
  simp only [select,EarlyPublicSelection.ordinary,parseAbsorb_absorbA,Option.bind_some]
  rw [hl,UnifiedLabels.row_label n (by omega),if_pos hn]

theorem opening (p : Params M Cv L) (T : Table (Addr L) State)
    (s : State) (data : Bytes) (hdata : data.length ≤ p.D)
    (n : Nat) (hn0 : 27 ≤ n) (hn1 : n ≤ 31) (hl : p.lbl n = UnifiedLabels.label n) :
    select p (absorbA p s (p.lbl n) data hdata) T =
      RawPublicOpeningWalk.select p T 2 4 s := by
  simp only [select,parseAbsorb_absorbA]
  rw [hl,UnifiedLabels.row_label n (by omega),if_neg (by omega),if_pos hn1]

theorem after_query (p : Params M Cv L) (T : Table (Addr L) State)
    (s : State) (data : Bytes) (hdata : data.length ≤ p.D)
    (hl : p.lbl 32 = UnifiedLabels.label 32) :
    select p (absorbA p s (p.lbl 32) data hdata) T =
      RawLatePublicSelector.select p T 2 4 (absorbA p s (p.lbl 32) data hdata) := by
  simp only [select,parseAbsorb_absorbA]
  rw [hl,UnifiedLabels.row_label 32 (by decide),if_neg (by decide),if_neg (by decide)]

#print axioms initial
#print axioms early
#print axioms opening
#print axioms after_query
end AspisR1.FullPublicSelection
end
