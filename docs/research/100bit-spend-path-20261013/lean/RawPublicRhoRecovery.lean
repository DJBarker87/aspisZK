import FullPublicSelection
import RawPublicOpeningAnchor
import RawLatePublicSelector
import R1UnifiedRecovery
import R1UnifiedOrdinaryFirstCell
import R1UnifiedQueryView
import R1QueryFirstRead
import R1QuerySamplerBridge
import R1JointContext

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawPublicRhoRecovery
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open TranscriptView
variable {M Cv W : Type} {L : Nat}

private theorem triple_fst_eq {A B C : Type} {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
    (h : (a₁, b₁, c₁) = (a₂, b₂, c₂)) : a₁ = a₂ := by
  cases h
  rfl
attribute [local irreducible] FullPublicSelection.select UnifiedProtocol.protocol UnifiedQueryRun.rhoAddress

/-- Public-free recovery at the rho frame, parametrized by the already-recorded
proof payload and trace prefix so fixed-row evaluator normalization stays outside. -/
theorem select_before_rho (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hlabels : ∀ i < 33, p.lbl i = UnifiedLabels.label i)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (Tout : Table (Addr L) State)
    (hT : Tout = tableBefore emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior)
      (UnifiedQueryRun.rhoAddress p hD H pub c1 payload)) :
    FullPublicSelection.select p (UnifiedQueryRun.rhoAddress p hD H pub c1 payload) Tout = some pub := by
  let π : UnifiedProtocol.Proof M := (c1, payload)
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub π.1 π.2 prior
  let a := UnifiedQueryRun.queryAddress p hD H pub π.1 π.2
  let c := UnifiedQueryRun.rhoAddress p hD H pub π.1 π.2
  let tableNow := tableBefore emptyTable tr c
  have hcurrent : c = UnifiedSteps.address p hD H pub π.1 π.2 32 := by
    simpa only [c, UnifiedQueryRun.rhoAddress] using
      (UnifiedSteps.payload_address p hD H pub π.1 π.2 32 (by decide))
  let rs := UnifiedRecords.records p hD H pub π.1 π.2 31
  let qr := UnifiedQueryRun.queryResult p hD H pub π.1 π.2
  let qs := QuerySampler.state p H (H a)
  let ss := UnifiedPhases.semanticState p hD H pub π.1 π.2
  let sb := UnifiedRecords.absorbed p hD H pub π.1 π.2
  let os := UnifiedPhases.openingState p hD H pub π.1 π.2
  let ob := fun j => UnifiedRecords.absorbed p hD H pub π.1 π.2 (27 + j)
  let om := fun j => payload (27 + j)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub π.1 π.2 prior
      hprior
  have hreads := UnifiedPrefixedReads.query_reads p hD extract decision H pub π.1 π.2 prior
  have hqueryRead : Read tr a := hreads.1
  have hca : c = absorbA p qr.2 (p.lbl 32)
      (p.enc (payload 32)) (p.encLen _) :=
    UnifiedQueryRun.rho_address p hD H pub π.1 π.2
  have hc : Read tr c := by
    have hr := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub π.1 π.2
      prior hl he 32 (by decide) (by decide)
    have hca' : c = UnifiedSteps.address p hD H pub π.1 π.2 32 := by
      simpa only [c, UnifiedQueryRun.rhoAddress] using
        (UnifiedSteps.payload_address p hD H pub π.1 π.2 32 (by decide))
    rw [hca']
    exact hr.1
  have hqa : a = absorbA p (os 4) (p.lbl 31)
      (p.enc (payload 31)) (p.encLen _) := by
    change UnifiedSampler.absorb p 31
      (UnifiedRun.transcript p hD H pub π.1 π.2 31) (payload 31) =
        absorbA p (UnifiedPhases.openingState p hD H pub π.1 π.2 4) _ _ _
    rw [UnifiedSteps.payload_address p hD H pub π.1 π.2 31 (by decide),
      UnifiedPhases.opening_previous]
    rfl
  have hparsea : parseAbsorb a = some (os 4, p.lbl 31,
      p.enc (payload 31)) := by
    rw [hqa, parseAbsorb_absorbA]
  have hparsec : parseAbsorb c = some (qr.2, p.lbl 32,
      p.enc (payload 32)) := by
    rw [hca, parseAbsorb_absorbA]
  have hpa : (parseAbsorb a).isSome := by rw [hparsea]; rfl
  have hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2 := by
    rw [hca]
    exact toBytes_absorbA p _ _ _ _
  have hbeforeq := QueryFirstRead.recover_query_before_endpoint p H tr Qtot hcons hQ hold qs
    (fun j _ => QuerySamplerBridge.state_step p H (H a) j)
    (fun j hj => (hreads.2 j hj).2) a c hqueryRead hc hpa rfl hcprefix
  obtain ⟨j, hj, hselected, hseek, _⟩ := hbeforeq
  have hqcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hold qs (j + 1)
    (fun t ht => QuerySamplerBridge.state_step p H (H a) t)
    (fun t ht => (hreads.2 t (by omega)).2) c a hc hqueryRead
    (by rw [← hselected]; exact hcprefix) rfl
  have hac : Before tr a c :=
    TableBeforeOrder.before_of_cell H tr hcons c a (qs 0) hqcells.1
  have hsroot := UnifiedPhases.semantic_root p hD H pub π.1 π.2
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits π.1) :=
    UnifiedPrefixedReads.initial_read p hD extract decision H pub π.1 π.2 prior
  have hsabs (j : Nat) (hj : j < 27) :
      sb j = H (absorbA p (ss j) (p.lbl j)
        (p.enc (payload j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.semanticState p hD H pub π.1 π.2 j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub π.1 π.2 j hj]
    rfl
  have hsstep (j : Nat) (hj : j < 27) :
      ss (j + 1) = H (advanceA p (sb j)) :=
    UnifiedPhases.semantic_step p hD H pub π.1 π.2 hl he j (by omega)
  have hsar (j : Nat) (hj : j < 27) :
      Read tr (absorbA p (ss j) (p.lbl j)
        (p.enc (payload j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.semanticState p hD H pub π.1 π.2 j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub π.1 π.2 j hj]
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub π.1 π.2
      prior hl he j (by omega) (by omega)).1
  have hsdr (j : Nat) (hj : j < 27) : Read tr (advanceA p (sb j)) :=
    (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub π.1 π.2
      prior hl he j (by omega) (by omega)).2.2
  have hr : Read tr (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega)
      (ss 27)) := by
    change Read tr (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega)
      (UnifiedPhases.semanticState p hD H pub π.1 π.2 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPrefixedReads.reseed_read p hD extract decision H pub π.1 π.2 prior
  have horoot : os 0 = H (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega)
      (ss 27)) := by
    change UnifiedPhases.openingState p hD H pub π.1 π.2 0 =
      H (OpeningReseedFrame.addr pub.tag (by have := pub.initFits; omega)
        (UnifiedPhases.semanticState p hD H pub π.1 π.2 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPhases.opening_root p hD H pub π.1 π.2
  have hoabs (j : Nat) (hj : j < 4) :
      ob j = H (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.openingState p hD H pub π.1 π.2 j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    rfl
  have hostep (j : Nat) (hj : j < 4) :
      os (j + 1) = H (advanceA p (ob j)) :=
    UnifiedPhases.opening_step p hD H pub π.1 π.2 hl he j (by omega)
  have hoar (j : Nat) (hj : j < 4) :
      Read tr (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.openingState p hD H pub π.1 π.2 j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub π.1 π.2
      prior hl he (27 + j) (by omega) (by omega)).1
  have hodr (j : Nat) (hj : j < 4) : Read tr (advanceA p (ob j)) :=
    (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub π.1 π.2
      prior hl he (27 + j) (by omega) (by omega)).2.2
  have hsD : ∀ j, (p.enc (payload j)).length ≤ p.D := fun j => p.encLen _
  have hoD : ∀ j, (p.enc (om j)).length ≤ p.D := fun j => p.encLen _
  have hwalk := RawPublicOpeningAnchor.walk_before_anchor p pub hpub htag π.1 pub.tag
    (by have := pub.initFits; omega) H tr Qtot hcons hQ hold htail 27 (by decide)
    (by decide) ss sb p.lbl (fun j => p.enc (payload j)) hsD
    hsroot hi hsabs hsstep hsar hsdr hr 4 4 (by decide) os ob
    (fun j => p.lbl (27 + j)) (fun j => p.enc (om j)) hoD horoot hoabs hostep hoar hodr
    a c hqueryRead (by rw [hqa]; exact toBytes_absorbA p _ _ _ _) hac
  have hopening : RawPublicOpeningWalk.select p tableNow pub.tag 4 (os 4) = some pub := by
    unfold RawPublicOpeningWalk.select
    change (RawPublicOpeningWalk.walk p tableNow pub.tag 4 (os 4)).map
      (fun result => result.1.1) = some pub
    rw [hwalk]
    rfl
  obtain ⟨htyped, _hfollow⟩ := UnifiedRecovery.recover_and_follow p hD extract decision
    H pub π.1 π.2 prior hprior hpub hl he Qtot hQ hold htail
  have hlen : rs.length = 31 := UnifiedRecords.records_length p hD H pub π.1 π.2 31
  let ctx : JointContext.Context M L := ⟨qr.2, a, π.1, rs,
    payload 31, payload 32⟩
  have hcontext : JointContext.parse p pub.pubBytes pub.tag 27 4 c tableNow = some ctx :=
    JointContext.parse_of_checks p pub.pubBytes pub.tag 27 4 c tableNow qr.2 _ _ a _
      (os 4) _ _ π.1 rs (payload 31) (payload 32)
      hparsec hseek hparsea htyped
      (by rw [hlen]; exact IndexedMessage.read_encoded p 31 (payload 31))
      (by rw [hlen]; exact IndexedMessage.read_encoded p 32 (payload 32))
  have hselected : ∀ previous ql qd,
      parseAbsorb ctx.queryAddress = some (previous, ql, qd) →
      RawPublicOpeningWalk.select p tableNow pub.tag 4 previous = some pub := by
    intro previous ql qd hparse
    have hparse' : parseAbsorb a = some (previous, ql, qd) := by
      simpa only [ctx] using hparse
    have heq : (os 4, p.lbl 31, p.enc (payload 31)) =
        (previous, ql, qd) := Option.some.inj (hparsea.symm.trans hparse')
    have hprev : previous = os 4 := (triple_fst_eq heq).symm
    rw [hprev]
    exact hopening
  have hlate := RawLatePublicSelector.select_of_joint_context p pub.pubBytes pub.tag 27 4 c tableNow
    ctx pub hcontext hselected
  rw [htag] at hlate
  have hresult := FullPublicSelection.after_query p tableNow qr.2
    (p.enc (payload 32)) (p.encLen _) (hlabels 32 (by decide))
  rw [← hca] at hresult
  have htable : Tout = tableNow := by
    simpa [tableNow, tr, c] using hT
  change FullPublicSelection.select p c Tout = some pub
  rw [htable]
  exact hresult.trans hlate

#print axioms AspisR1.RawPublicRhoRecovery.select_before_rho
end AspisR1.RawPublicRhoRecovery
end
