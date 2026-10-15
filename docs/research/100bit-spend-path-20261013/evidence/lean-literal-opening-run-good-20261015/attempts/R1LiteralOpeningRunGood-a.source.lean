import R1LiteralOpeningGood
import R1LiteralByteRunFacts
import R1LiteralGammaSample

/-! In an actual all-byte sampler transcript, successful terminal decoding
and absence of classifier hits imply the existing opening Good predicate.
Nonzero gamma is derived from its sampler. This does not establish accepted
reader coverage, D3, source correspondence, or a probability bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningRunGood

open LiteralTranscript
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
abbrev E := LiteralTranscript.E

attribute [local irreducible] ConcreteBinding.gammaBad ConcreteBinding.kappaBad
  ConcreteBinding.firstBad ConcreteBinding.secondBad

theorem gamma_nonzero_of_transcript_read
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : Public) (pf : LiteralProtocol.Proof) (n : Nat) (hn : 32 ≤ n)
    (d : MatchingSupport.Data E)
    (hread : LiteralMatchingData.read
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds = some d) :
    d.gamma ≠ 0 := by
  let rs := ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds
  have hlen : rs.length = n := LiteralByteRunFacts.transcript_round decoder H pub pf n
  have hi : 27 < rs.length := by omega
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hc, hs, hr31, hw, hg, hk, ha0, ha1, hd⟩ :=
    LiteralMatchingFacts.read_success_components rs d hread
  have h27 := (LiteralReadAtFacts.readGamma_current rs staged.toGamma
    (LiteralStageFacts.readSecond_gamma rs staged hs)).2.2
  have hv := LiteralIndexedPrefix.readAt_success_index_valid rs 27 hi _ _ h27
  have hidx : rs[27]? = some (pf 27,
      (eval H (LiteralByteSampler.samp 27
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 27)
        (pf 27)).toProgram).2) :=
    LiteralByteRunFacts.transcript_index decoder H pub pf n 27 (by omega)
  rw [List.getElem?_eq_getElem hi] at hidx
  have heq := Option.some.inj hidx
  rw [heq] at hv
  obtain ⟨actual, state, hsample, hnonzero⟩ :=
    LiteralGammaSample.valid_row27_nonzero H
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 27) (pf 27) hv
  have hc27 : LiteralChallengeRead.ordinaryAt rs 27 = some d.gamma := by
    rw [hd]
    exact hg
  have hx := LiteralIndexedPrefix.ordinaryAt_success_index_value rs 27 hi d.gamma hc27
  rw [heq] at hx
  have he : TranscriptView.Value.ordinary actual = TranscriptView.Value.ordinary d.gamma := by
    exact (congrArg (fun c : LiteralTranscript.Challenge => c.1) hsample).symm.trans hx
  have hactual : actual = d.gamma := TranscriptView.Value.ordinary.inj he
  rw [← hactual]
  exact hnonzero

theorem good_of_transcript_read_noHit
    (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : Public) (pf : LiteralProtocol.Proof) (n : Nat) (hn : 32 ≤ n)
    (d : MatchingSupport.Data E)
    (hread : LiteralMatchingData.read
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds = some d)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds) :
    MatchingSupport.Good d := by
  have hlen : ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds.length = n :=
    LiteralByteRunFacts.transcript_round decoder H pub pf n
  exact LiteralOpeningGood.good_of_read_noHit pub _ d (by omega) hread
    (gamma_nonzero_of_transcript_read decoder H pub pf n hn d hread) hno

#print axioms gamma_nonzero_of_transcript_read
#print axioms good_of_transcript_read_noHit

end AspisR1.LiteralOpeningRunGood
end
