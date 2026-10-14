import R1UnifiedDecoder
import R1UnifiedOrdinaryFirstCell
import R1UnifiedReseedView
import R1UnifiedQueryView

/-! The actual first-cell address selects its own decoder component. The
label schedule and public length remain explicit parameter premises. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedDispatchAddress

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem firstCell_nonzero (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat) (hn0 : n ≠ 0) :
    firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (c1, payload) n) =
      some (UnifiedSteps.address p hD H pub c1 payload n) := by
  by_cases h26 : n = 26
  · subst n
    exact UnifiedReseedView.firstCell_eq p hD extract H pub c1 payload
  by_cases h31 : n = 31
  · subst n
    exact UnifiedQueryView.firstCell_eq p hD extract H pub c1 payload
  exact UnifiedOrdinaryFirstCell.firstCell_eq p hD extract H pub c1 payload n hn0 h26 h31

theorem decode_at_first (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) (T : Table (Addr L) State)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub π n) = some a) :
    UnifiedDecoder.decode p hD pub a T = UnifiedDecoder.component p hD pub n a T := by
  by_cases hn0 : n = 0
  · subst n
    have hc := UnifiedFramework.initial_firstCell p hD extract H pub π.1 π.2
    have ha : a = PublicInitFrame.addr pub.pubBytes pub.initFits π.1 :=
      Option.some.inj (hfirst.symm.trans hc)
    subst a
    exact UnifiedDecoder.decode_of_init_parse p hD pub _ T π.1
      (PublicInitParse.parse_addr pub.pubBytes hpub pub.initFits π.1)
  · have hc := firstCell_nonzero p hD extract H pub π.1 π.2 n hn0
    have ha : a = UnifiedSteps.address p hD H pub π.1 π.2 n :=
      Option.some.inj (hfirst.symm.trans hc)
    subst a
    exact UnifiedDecoder.decode_of_absorb p hD pub T
      (UnifiedRecords.previous p hD H pub π.1 π.2 n) n
      (p.enc (π.2 n)) (p.encLen (π.2 n)) hn (hl n hn)

#print axioms firstCell_nonzero
#print axioms decode_at_first

end AspisR1.UnifiedDispatchAddress
end
