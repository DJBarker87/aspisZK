import R1UnifiedSemanticFacts
import R1UnifiedReseedView
import R1UnifiedReseedDecoder
import R1PrefixReseedTrace

/-! The completing decoder reconstructs the semantic-to-opening reseed row 26
from the actual prefixed verifier trace. The budget, collision exclusion,
and row-zero codec hypotheses remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedReseedInjection

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload 26
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      UnifiedReseedDecoder.decode p pub c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub c1 payload 26,
          UnifiedRun.message c1 payload 26,
          UnifiedRun.challenge p hD H pub c1 payload 26) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload 26
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload 26
  let ctx : UnifiedSemanticContext.Context M := ⟨c1, rs, payload 26⟩
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hreads := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
    prior hl he 26 (by omega) (by omega)
  have htyped := UnifiedSemanticRecovery.typed_before_row p hD extract decision H pub
    c1 payload prior hprior hpub hl he Qtot hQ hold 26 (by decide) (by decide)
  have hfacts := UnifiedSemanticFacts.semantic_records_have_cells_and_squeeze_reads
    p hD extract decision H pub c1 payload prior hprior hl he Qtot hQ hold 26 (by decide) (by decide)
  have hparse : parseAbsorb c = some
      (UnifiedRecords.previous p hD H pub c1 payload 26, p.lbl 26, p.enc (payload 26)) :=
    parseAbsorb_absorbA p _ _ _ _
  have hlen : rs.length = 26 := UnifiedRecords.records_length p hD H pub c1 payload 26
  have hcontext : UnifiedSemanticContext.parse p pub.pubBytes c T = some ctx :=
    UnifiedSemanticContext.parse_of_checks p pub.pubBytes c T _ _ _ c1 rs (payload 26)
      hparse htyped (by rw [hlen]; exact IndexedMessage.read_encoded p 26 (payload 26))
  have h62 : 62 ≤ L := by have := pub.initFits; omega
  have hr := UnifiedPrefixedReads.reseed_read p hD extract decision H pub c1 payload prior
  have hfollow := PrefixReseedTrace.follows_after_prefix p pub.tag h62 H tr Qtot hcons
    hQ hold htail c hreads.1 (by rw [hparse]; rfl) hreads.2.1 hreads.2.2
    hr rs hfacts.1 hfacts.2
  refine ⟨UnifiedReseedDecoder.own p pub c,
    (PrefixAnswers.missing p T rs).map (fun b => (b, none)),
    UnifiedSemanticDecoder.output p pub T ctx,
    UnifiedReseedDecoder.decode_of_parse p pub c T ctx hcontext hlen, ?_⟩
  have hm := UnifiedSemanticDecoder.follows_map pub ctx (PrefixNextLaw.output p T rs)
    (traceFrom tr c) (UnifiedReseedDecoder.own p pub c)
    ((PrefixAnswers.missing p T rs).map fun b => (b, none)) T _ hfollow
  rw [hlen] at hm
  exact hm.trans (congrArg some
    (UnifiedReseedView.actual_output p hD H pub c1 payload hl he))

#print axioms decodes_and_follows

end AspisR1.UnifiedReseedInjection
end
