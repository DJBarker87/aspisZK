import R1UnifiedSemanticFacts
import R1UnifiedSemanticActualView
import R1PrefixNextTrace

/-! The completing decoder reconstructs every ordinary semantic row 1..25
from the actual prefixed verifier trace. The budget, collision exclusion,
and row-zero codec hypotheses remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticInjection

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
    (n : Nat) (hn : 0 < n) (hn26 : n < 26) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload n
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      UnifiedSemanticDecoder.decode p pub c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub c1 payload n,
          UnifiedRun.message c1 payload n,
          UnifiedRun.challenge p hD H pub c1 payload n) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload n
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload n
  let ctx : UnifiedSemanticContext.Context M := ⟨c1, rs, payload n⟩
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hreads := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
    prior hl he n (by omega) (by omega)
  have htyped := UnifiedSemanticRecovery.typed_before_row p hD extract decision H pub
    c1 payload prior hprior hpub hl he Qtot hQ hold n hn (by omega)
  have hfacts := UnifiedSemanticFacts.semantic_records_have_cells_and_squeeze_reads
    p hD extract decision H pub c1 payload prior hprior hl he Qtot hQ hold n hn (by omega)
  have hparse : parseAbsorb c = some
      (UnifiedRecords.previous p hD H pub c1 payload n, p.lbl n, p.enc (payload n)) :=
    parseAbsorb_absorbA p _ _ _ _
  have hlen : rs.length = n := UnifiedRecords.records_length p hD H pub c1 payload n
  have hcontext : UnifiedSemanticContext.parse p pub.pubBytes c T = some ctx :=
    UnifiedSemanticContext.parse_of_checks p pub.pubBytes c T _ _ _ c1 rs (payload n)
      hparse htyped (by rw [hlen]; exact IndexedMessage.read_encoded p n (payload n))
  have hfollow := PrefixNextTrace.follows_after_prefix p H tr Qtot hcons hQ hold
    c hreads.1 (by rw [hparse]; rfl) hreads.2.1 hreads.2.2 rs hfacts.1 hfacts.2
  refine ⟨QueryNextLaw.own p c,
    (PrefixAnswers.missing p T rs).map (fun b => (b, none)),
    UnifiedSemanticDecoder.output p pub T ctx,
    UnifiedSemanticDecoder.decode_of_parse p pub c T ctx hcontext
      (by change 0 < rs.length; rw [hlen]; exact hn)
      (by change rs.length < 26; rw [hlen]; exact hn26), ?_⟩
  have hm := UnifiedSemanticDecoder.follows_map pub ctx (PrefixNextLaw.output p T rs)
    (traceFrom tr c) (QueryNextLaw.own p c)
    ((PrefixAnswers.missing p T rs).map fun b => (b, none)) T _ hfollow
  rw [hlen] at hm
  exact hm.trans (congrArg some
    (UnifiedSemanticActualView.actual_output p hD H pub c1 payload hl he n hn hn26))

#print axioms decodes_and_follows

end AspisR1.UnifiedSemanticInjection
end
