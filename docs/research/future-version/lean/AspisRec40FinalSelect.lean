import RawPublicRhoRecovery
import AspisRec40FinalContext
import AspisRows40FinalByte

/-! Public selection at the table before row n's frame (work order W2),
33 ≤ n < 40, on the 40-row address-level run, at R1's selected parameters.

Copy of R1's row-32 selection `RawPublicRhoRecovery.select_before_rho` (the
address-level step under `RWireRawFullPublicRun.select_actual_run`), with the
table taken before row n's frame:
- R1's row-32 context at `T_n` is `AspisRec40.FinalContext.joint_at`;
- the public opening walk at `T_n` is R1's anchor-parametric
  `RawPublicOpeningAnchor.walk_before_anchor` with anchor row n's frame;
- `RawLatePublicSelector.select_of_joint_context` and
  `FullPublicSelection.after_query` give R1's selector at row 32's frame;
- `AspisRows40.FinalByte.select` first walks back `n - 33` rows
  (`AspisRec40.FinalContext.back_run`).

Premises: those of `FollowStatement.FollowClaim` and R1's tag premise
`htag : pub.tag = 2`, which R1's own row-32 selection carries
(`select_before_rho`, `select_actual_run`): the selector reads the reseed
frame with the fixed tag 2, the run writes it with `pub.tag`. Model level. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalSelect
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

abbrev M := SelectedTranscriptParams.Message
abbrev Cv := AspisWideTower.WideExact
abbrev L := SelectedTranscriptParams.L
abbrev p := SelectedTranscriptParams.params

private theorem triple_fst_eq {A B C : Type} {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
    (h : (a₁, b₁, c₁) = (a₂, b₂, c₂)) : a₁ = a₂ := by
  cases h
  rfl

attribute [local irreducible] FullPublicSelection.select

/-- W2: the public statement selected at row n's frame and the table before it. -/
theorem select_at {W : Type} (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    AspisRows40.FinalByte.select n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable
          (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) = some pub := by
  let tr := AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior
  let cn := UnifiedSteps.address p hD H pub c1 payload n
  let Tn := tableBefore emptyTable tr cn
  let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
  let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
  let ss := UnifiedPhases.semanticState p hD H pub c1 payload
  let sb := UnifiedRecords.absorbed p hD H pub c1 payload
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  let ob := fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j)
  let om := fun j => payload (27 + j)
  let qs := QuerySampler.state p H (H a)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    AspisRec40.FinalRun.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1) :=
    AspisRec40.FinalRun.initial_read p hD extract decision H pub c1 payload prior
  have hreads (i : Nat) (hi : i < 33) (hi31 : i ≠ 31) :=
    AspisRec40.FinalRun.ordinary_reads p hD extract decision H pub c1 payload prior hl he i
      (by omega) hi31
  have hsabs (j : Nat) (hj : j < 27) :
      sb j = H (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    rfl
  have hsar (j : Nat) (hj : j < 27) :
      Read tr (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    exact (hreads j (by omega) (by omega)).1
  have h62 : 62 ≤ L := by have := pub.initFits; omega
  have hr : Read tr (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change Read tr (OpeningReseedFrame.addr pub.tag h62
      (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact AspisRec40.FinalRun.reseed_read p hD extract decision H pub c1 payload prior
  have horoot : os 0 = H (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change UnifiedPhases.openingState p hD H pub c1 payload 0 =
      H (OpeningReseedFrame.addr pub.tag h62
        (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPhases.opening_root p hD H pub c1 payload
  have hoabs (j : Nat) (hj : j < 4) :
      ob j = H (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    rfl
  have hoar (j : Nat) (hj : j < 4) :
      Read tr (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    exact (hreads (27 + j) (by omega) (by omega)).1
  have hqr := AspisRec40.FinalRun.query_reads p hD extract decision H pub c1 payload prior
  have ha : Read tr a := hqr.1
  have hca0 : c = UnifiedSteps.address p hD H pub c1 payload 32 :=
    UnifiedSteps.payload_address p hD H pub c1 payload 32 (by decide)
  have hc : Read tr c := by rw [hca0]; exact (hreads 32 (by decide) (by decide)).1
  have hqa : a = absorbA p (os 4) (p.lbl 31) (p.enc (payload 31)) (p.encLen _) := by
    change UnifiedSampler.absorb p 31 (UnifiedRun.transcript p hD H pub c1 payload 31)
      (payload 31) = absorbA p (UnifiedPhases.openingState p hD H pub c1 payload 4) _ _ _
    rw [UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide),
      UnifiedPhases.opening_previous]
    rfl
  have hca : c = absorbA p (QueryFirstRead.result p H qs).2 (p.lbl 32)
      (p.enc (payload 32)) (p.encLen _) :=
    UnifiedQueryRun.rho_address p hD H pub c1 payload
  have hparsea : parseAbsorb a = some (os 4, p.lbl 31, p.enc (payload 31)) := by
    rw [hqa, parseAbsorb_absorbA]
  have hpa : (parseAbsorb a).isSome := by rw [hparsea]; rfl
  have hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2 := by
    rw [hca]; exact toBytes_absorbA p _ _ _ _
  have hcn : Before tr c cn := by
    rw [hca0]
    exact (AspisRec40.FinalBefore.run_cells p hD extract decision H pub c1 payload prior hprior
      hl he Qtot hQ hold n hhi 32 (le_refl _) (by omega)).1
  -- the query address is read before row 32's frame (R1's route)
  have hqstep : ∀ j < 8, qs (j + 1) = H (advanceA p (qs j)) :=
    fun j _ => QuerySamplerBridge.state_step p H (H a) j
  have hqadv : ∀ j < 8, Read tr (advanceA p (qs j)) := fun j hj => (hqr.2 j hj).2
  obtain ⟨k, hk, hselected, _, _⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs hqstep hqadv a c ha hc hpa rfl hcprefix
  have hqcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hold qs (k + 1)
    (fun t _ => hqstep t (by omega)) (fun t _ => hqadv t (by omega))
    c a hc ha (by rw [← hselected]; exact hcprefix) rfl
  have hac : Before tr a c :=
    TableBeforeOrder.before_of_cell H tr hcons c a (qs 0) hqcells.1
  -- the public opening walk at anchor row n's frame
  have hwalk := RawPublicOpeningAnchor.walk_before_anchor p pub hpub htag c1 pub.tag h62
    H tr Qtot hcons hQ hold htail 27 (by decide) (le_refl _)
    ss sb p.lbl (fun j => p.enc (payload j)) (fun j => p.encLen (payload j))
    (UnifiedPhases.semantic_root p hD H pub c1 payload) hi hsabs
    (fun j hj => UnifiedPhases.semantic_step p hD H pub c1 payload hl he j (by omega)) hsar
    (fun j hj => (hreads j (by omega) (by omega)).2.2) hr
    4 4 (le_refl _) os ob (fun j => p.lbl (27 + j)) (fun j => p.enc (om j))
    (fun j => p.encLen (om j)) horoot hoabs
    (fun j hj => UnifiedPhases.opening_step p hD H pub c1 payload hl he j (by omega)) hoar
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.2)
    a cn ha (by rw [hqa]; exact toBytes_absorbA p _ _ _ _) (before_trans tr hac hcn)
  have hopening : RawPublicOpeningWalk.select p Tn pub.tag 4 (os 4) = some pub := by
    unfold RawPublicOpeningWalk.select
    change (RawPublicOpeningWalk.walk p Tn pub.tag 4 (os 4)).map
      (fun result => result.1.1) = some pub
    rw [hwalk]
    rfl
  -- R1's row-32 context at T_n
  have hcontext := AspisRec40.FinalContext.joint_at p hD extract decision H pub c1 payload prior
    hprior hpub hl he Qtot hQ hold htail n hlo hhi
  have hsel : ∀ previous ql qd,
      parseAbsorb (AspisRec40.FollowStatement.jointCtx p hD H pub c1 payload).queryAddress =
        some (previous, ql, qd) →
      RawPublicOpeningWalk.select p Tn pub.tag 4 previous = some pub := by
    intro previous ql qd hparse
    have hparse' : parseAbsorb a = some (previous, ql, qd) := hparse
    have heq : (os 4, p.lbl 31, p.enc (payload 31)) = (previous, ql, qd) :=
      Option.some.inj (hparsea.symm.trans hparse')
    rw [← triple_fst_eq heq]
    exact hopening
  have hlate := RawLatePublicSelector.select_of_joint_context p pub.pubBytes pub.tag 27 4
    (UnifiedSteps.address p hD H pub c1 payload 32) Tn _ pub hcontext hsel
  rw [htag] at hlate
  have hresult := FullPublicSelection.after_query p Tn
    (UnifiedRecords.previous p hD H pub c1 payload 32) (p.enc (payload 32)) (p.encLen _) rfl
  have h32 : FullPublicSelection.select p (UnifiedSteps.address p hD H pub c1 payload 32) Tn =
      some pub := hresult.trans hlate
  -- the walk back from row n's frame to row 32's frame
  have hb := AspisRec40.FinalContext.back_run p hD extract decision H pub c1 payload prior
    hprior hl he Qtot hQ hold n hhi (n - 33) (by omega)
  rw [show 33 + (n - 33) = n by omega] at hb
  unfold AspisRows40.FinalByte.select
  rw [AspisRec40.FinalContext.parse_address]
  simp only [Option.bind_some]
  rw [hb]
  simp only [Option.bind_some]
  exact h32

#print axioms triple_fst_eq
#print axioms select_at

end AspisRec40.FinalSelect
end
