import R1UnifiedOpeningRecovery
import R1UnifiedOpeningDecoder
import R1UnifiedQueryDecoder
import R1UnifiedQueryView
import R1PrefixQueryTrace

/-! The completing query decoder reconstructs the query row from the actual
prefixed verifier trace, with the existing budget and collision exclusions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryInjection

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
    let c := UnifiedSteps.address p hD H pub c1 payload 31
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      UnifiedQueryDecoder.decode p pub c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub c1 payload 31,
          UnifiedRun.message c1 payload 31,
          UnifiedRun.challenge p hD H pub c1 payload 31) := by
  dsimp only
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload 31
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload 31
  let ctx : UnifiedSemanticContext.Context M := ⟨c1, rs, payload 31⟩
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hqueryreads := UnifiedPrefixedReads.query_reads p hD extract decision H pub c1 payload prior
  have hc : Read tr c := by
    dsimp [c] at hqueryreads ⊢
    exact hqueryreads.1
  have hparse : parseAbsorb c =
      some (UnifiedRecords.previous p hD H pub c1 payload 31,
        p.lbl 31, p.enc (payload 31)) := by
    dsimp [c]
    exact parseAbsorb_absorbA p _ _ _ _
  have hparsec : (parseAbsorb c).isSome := by
    rw [hparse]
    rfl
  have hreads : ∀ j < 8,
      Read tr (squeezeA p (QuerySampler.state p H (H c) j)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) j)) := by
    intro j hj
    dsimp [c] at hqueryreads
    exact hqueryreads.2 j hj
  obtain ⟨htyped, hknown, hprefixreads⟩ :=
    UnifiedOpeningRecovery.recover_before_row p hD extract decision H pub c1 payload
      prior hprior hpub hl he Qtot hQ hold htail 4 (by omega)
  have hlen : rs.length = 31 := by
    change (UnifiedRecords.records p hD H pub c1 payload 31).length = 31
    exact UnifiedRecords.records_length p hD H pub c1 payload 31
  have hcontext : UnifiedOpeningDecoder.parse p pub c T = some ctx :=
    UnifiedOpeningDecoder.parse_of_checks p pub c T _ _ _ c1 rs (payload 31)
      hparse (by rw [UnifiedPhases.opening_previous] at htyped; exact htyped)
      (by rw [hlen]; exact IndexedMessage.read_encoded p 31 (payload 31))
  have hfollow := PrefixQueryTrace.follows_after_prefix p H tr Qtot hcons hQ hold
    c hc hparsec 8 hreads rs hknown hprefixreads
    (UnifiedQueryDecoder.output p pub T ctx)
  refine ⟨UnifiedQueryDecoder.own p c,
    (PrefixAnswers.missing p T rs).map (fun b => (b, none)),
    UnifiedQueryDecoder.output p pub T ctx,
    UnifiedQueryDecoder.decode_of_parse p pub c T ctx hcontext hlen, ?_⟩
  have hT : ∀ b v, T b = some v → v = H b :=
    fun b v hv =>
      (DuplexPrefixTable.table_consistent H tr hcons c b v hv).1
  have hc_eq : c = UnifiedQueryRun.queryAddress p hD H pub c1 payload := by
    change UnifiedSteps.address p hD H pub c1 payload 31 =
      UnifiedQueryRun.queryAddress p hD H pub c1 payload
    dsimp [UnifiedQueryRun.queryAddress]
    rw [← UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide)]
  have hactual := UnifiedQueryView.actual_output p hD H pub c1 payload hl he T hT
  rw [← hc_eq] at hactual
  have hfollow' :
      bfollow (UnifiedQueryDecoder.output p pub T ctx) (traceFrom tr c)
          (UnifiedQueryDecoder.own p c)
          ((PrefixAnswers.missing p T rs).map (fun b => (b, none))) T =
        some (UnifiedQueryDecoder.output p pub T ctx
          ([H c] ++ (List.range 8).map
            (fun k => QuerySampler.state p H (H c) (k + 1))
          (List.map H (PrefixAnswers.missing p T rs) ++ (List.range 8).map
            (fun k => H (squeezeA p (QuerySampler.state p H (H c) k)))) := by
    simpa only [UnifiedQueryDecoder.own, QueryBackgroundChain.chainBS, T, rs] using hfollow
  rw [hfollow']
  exact congrArg some (by
    simpa only [QueryStateList.states, QueryStateList.blocks,
      QueryBackgroundChain.map_range_succ, QuerySamplerBridge.state_initial] using hactual)

#print axioms decodes_and_follows

end AspisR1.UnifiedQueryInjection
end
