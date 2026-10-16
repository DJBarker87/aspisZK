import SemanticPublicSelection

/-! Concrete initial and ordinary public selectors. The ordinary selector
rewinds the input address's predecessor state through the current table. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.EarlyPublicSelection
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
variable {M Cv W : Type} {L : Nat}

def initial (a : Addr L) : Option (UnifiedSampler.Public L) :=
  (RawPublicInitParser.parse a).map Prod.fst

def ordinary (p : Params M Cv L) (a : Addr L) (T : Table (Addr L) State) :
    Option (UnifiedSampler.Public L) :=
  (parseAbsorb a).bind fun (endpoint,_,_) => SemanticPublicSelection.select p T endpoint

theorem initial_addr (pub : UnifiedSampler.Public L) (root : State)
    (hlen : pub.pubBytes.length < 2^32) (htag : pub.tag = 2) :
    initial (PublicInitFrame.addr pub.pubBytes pub.initFits root) = some pub := by
  unfold initial
  rw [RawPublicInitParser.of_fixed_parse pub _ root htag
    (PublicInitParse.parse_addr pub.pubBytes hlen pub.initFits root)]
  rfl

theorem ordinary_absorb (p : Params M Cv L) (s : State) (label : Byte)
    (data : Bytes) (hd : data.length ≤ p.D) (T : Table (Addr L) State) :
    ordinary p (absorbA p s label data hd) T = SemanticPublicSelection.select p T s := by
  unfold ordinary
  rw [parseAbsorb_absorbA]
  rfl

theorem ordinary_before_row (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → TranscriptView.Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hn : 0 < n) (hn26 : n ≤ 26) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let a := UnifiedSteps.address p hD H pub c1 payload n
    ordinary p a (tableBefore emptyTable tr a) = some pub := by
  dsimp only
  change ordinary p (absorbA p (UnifiedRecords.previous p hD H pub c1 payload n)
      (p.lbl n) (p.enc (payload n)) (p.encLen (payload n))) _ = _
  rw [ordinary_absorb]
  exact SemanticPublicSelection.select_before_row p hD extract decision H pub c1 payload
    prior hprior hpub htag hl he Qtot hQ hold n hn hn26

#print axioms initial_addr
#print axioms ordinary_absorb
#print axioms ordinary_before_row
end AspisR1.EarlyPublicSelection
end
