import R1UnifiedRecovery
import R1JointUnifiedDecoder
import R1JointActualView

/-! The guarded row-32 decoder recovers and follows the actual unified run.
This is the rho case only. The public-length/row-zero codec premises,
first-read budget and collision exclusions remain explicit; it is not the
full decoder dispatch or a numerical Fiat--Shamir/security theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRhoInjection

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
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedTraceReads.trace p hD extract decision H pub c1 payload) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedTraceReads.trace p hD extract decision H pub c1 payload))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (UnifiedTraceReads.trace p hD extract decision H pub c1 payload)) :
    let tr := UnifiedTraceReads.trace p hD extract decision H pub c1 payload
    let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
    let T := tableBefore emptyTable tr c
    ∃ own pend g,
      JointUnifiedDecoder.decode p pub 27 4 c T = some (own, pend, g) ∧
      bfollow g (traceFrom tr c) own pend T =
        some (UnifiedRun.transcript p hD H pub c1 payload 32,
          UnifiedRun.message c1 payload 32,
          UnifiedRun.challenge p hD H pub c1 payload 32) := by
  dsimp only
  let tr := UnifiedTraceReads.trace p hD extract decision H pub c1 payload
  let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
  let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
  let T := tableBefore emptyTable tr c
  let rs := UnifiedRecords.records p hD H pub c1 payload 31
  let qr := UnifiedQueryRun.queryResult p hD H pub c1 payload
  let qs := QuerySampler.state p H (H a)
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  obtain ⟨htyped, hfollow⟩ := UnifiedRecovery.recover_and_follow p hD extract decision
    H pub c1 payload hpub hl he Qtot hQ hold htail
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedTraceReads.trace_consistent p hD extract decision H pub c1 payload
  have hreads := UnifiedTraceReads.query_reads p hD extract decision H pub c1 payload
  have ha : Read tr a := hreads.1
  have hc : Read tr c := by
    have hr := UnifiedTraceReads.ordinary_reads p hD extract decision H pub c1 payload
      hl he 32 (by decide) (by decide)
    have hca : c = UnifiedSteps.address p hD H pub c1 payload 32 :=
      UnifiedSteps.payload_address p hD H pub c1 payload 32 (by decide)
    rw [hca]
    exact hr.1
  have hqa : a = absorbA p (os 4) (p.lbl 31) (p.enc (payload 31)) (p.encLen _) := by
    change UnifiedSampler.absorb p 31 (UnifiedRun.transcript p hD H pub c1 payload 31)
      (payload 31) = absorbA p (UnifiedPhases.openingState p hD H pub c1 payload 4) _ _ _
    rw [UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide),
      UnifiedPhases.opening_previous]
    rfl
  have hca : c = absorbA p qr.2 (p.lbl 32) (p.enc (payload 32)) (p.encLen _) :=
    UnifiedQueryRun.rho_address p hD H pub c1 payload
  have hparsea : parseAbsorb a = some (os 4, p.lbl 31, p.enc (payload 31)) := by
    rw [hqa, parseAbsorb_absorbA]
  have hparsec : parseAbsorb c = some (qr.2, p.lbl 32, p.enc (payload 32)) := by
    rw [hca, parseAbsorb_absorbA]
  have hpa : (parseAbsorb a).isSome := by rw [hparsea]; rfl
  have hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2 := by
    rw [hca]; exact toBytes_absorbA p _ _ _ _
  obtain ⟨j, hj, hselected, hseek, _⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs
    (fun j _ => QuerySamplerBridge.state_step p H (H a) j)
    (fun j hj => (hreads.2 j hj).2) a c ha hc hpa rfl hcprefix
  have hlen : rs.length = 31 := UnifiedRecords.records_length p hD H pub c1 payload 31
  let ctx : JointContext.Context M L := ⟨qr.2, a, c1, rs, payload 31, payload 32⟩
  have hcontext : JointContext.parse p pub.pubBytes pub.tag 27 4 c T = some ctx :=
    JointContext.parse_of_checks p pub.pubBytes pub.tag 27 4 c T qr.2 _ _ a _
      (os 4) _ _ c1 rs (payload 31) (payload 32) hparsec hseek hparsea htyped
      (by rw [hlen]; exact IndexedMessage.read_encoded p 31 (payload 31))
      (by rw [hlen]; exact IndexedMessage.read_encoded p 32 (payload 32))
  refine ⟨QueryNextLaw.own p c,
    (JointPrefixAnswers.missing p T rs qr.2).map (fun b => (b, none)),
    (fun x as => JointTranscriptView.view pub (JointDecoder.output p T ctx x as)),
    JointUnifiedDecoder.decode_of_parse p pub 27 4 c T ctx hcontext hlen, ?_⟩
  have hf := JointDecoder.follows_of_joint p T ctx c (traceFrom tr c)
    ((completeRounds p emptyTable H 0 rs, some (a, qr)),
      (p.σ 32 (H (squeezeA p (H c))), H (advanceA p (H c))))
    (by simpa only [ctx, hlen] using hfollow)
  have hm := JointTranscriptView.follows_map pub (JointDecoder.output p T ctx)
    (traceFrom tr c) (QueryNextLaw.own p c)
    ((JointPrefixAnswers.missing p T rs qr.2).map fun b => (b, none)) T _ hf
  change _ = some (JointTranscriptView.view pub
    (c1, payload 31, payload 32,
      ((completeRounds p emptyTable H 0 rs, some (a, qr)),
        (p.σ 32 (H (squeezeA p (H c))), H (advanceA p (H c)))))) at hm
  rw [JointActualView.actual_output p hD H pub c1 payload hl he] at hm
  exact hm

#print axioms decodes_and_follows

end AspisR1.UnifiedRhoInjection
end
