import R1UnifiedOpeningRecovery
import R1UnifiedOpeningDecoder
import R1UnifiedOpeningView
import R1PrefixNextTrace

/-! The completing decoder reconstructs each ordinary opening row 27..30
from the actual prefixed verifier trace. The budget, collision exclusion,
and row-zero codec hypotheses remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningInjection

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
      emptyTable (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (k : Nat) (hk : k < 4) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload (27 + k)
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      UnifiedOpeningDecoder.decode p pub c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub c1 payload (27 + k),
          UnifiedRun.message c1 payload (27 + k),
          UnifiedRun.challenge p hD H pub c1 payload (27 + k)) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload (27 + k)
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload (27 + k)
  let ctx : UnifiedSemanticContext.Context M := ⟨c1, rs, payload (27 + k)⟩
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hreads := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
    prior hl he (27 + k) (by omega) (by omega)
  obtain ⟨htyped, hknown, hprefixreads⟩ := UnifiedOpeningRecovery.recover_before_row
    p hD extract decision H pub c1 payload prior hprior hpub hl he Qtot hQ hold htail
    k (by omega)
  have hparse : parseAbsorb c = some
      (UnifiedRecords.previous p hD H pub c1 payload (27 + k), p.lbl (27 + k), p.enc (payload (27 + k))) :=
    parseAbsorb_absorbA p _ _ _ _
  have hlen : rs.length = (27 + k) := UnifiedRecords.records_length p hD H pub c1 payload (27 + k)
  have hcontext : UnifiedOpeningDecoder.parse p pub c T = some ctx :=
    UnifiedOpeningDecoder.parse_of_checks p pub c T _ _ _ c1 rs (payload (27 + k))
      hparse (by rw [UnifiedPhases.opening_previous] at htyped; exact htyped) (by rw [hlen]; exact IndexedMessage.read_encoded p (27 + k) (payload (27 + k)))
  have hfollow := PrefixNextTrace.follows_after_prefix p H tr Qtot hcons hQ hold
    c hreads.1 (by rw [hparse]; rfl) hreads.2.1 hreads.2.2 rs hknown hprefixreads
  refine ⟨QueryNextLaw.own p c,
    (PrefixAnswers.missing p T rs).map (fun b => (b, none)),
    UnifiedSemanticDecoder.output p pub T ctx,
    UnifiedOpeningDecoder.decode_of_parse p pub c T ctx hcontext
      (by change 27 ≤ rs.length; rw [hlen]; omega)
      (by change rs.length < 31; rw [hlen]; omega), ?_⟩
  have hm := UnifiedSemanticDecoder.follows_map pub ctx (PrefixNextLaw.output p T rs)
    (traceFrom tr c) (QueryNextLaw.own p c)
    ((PrefixAnswers.missing p T rs).map fun b => (b, none)) T _ hfollow
  rw [hlen] at hm
  exact hm.trans (congrArg some
    (UnifiedOpeningView.actual_output p hD H pub c1 payload hl he k hk))

#print axioms decodes_and_follows

end AspisR1.UnifiedOpeningInjection
end
