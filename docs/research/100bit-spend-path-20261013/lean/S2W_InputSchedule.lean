import S2W_NativeConsolidation
import S2W_SiteSchedule

/-! Twelve-field consolidation on ONE fixed-invocation observation. Account
before/after are arbitrary actual observation parameters, not replaced by a
logical commit spec. This deliberately exposes the two remaining frame fields.
InputScheduleFacts is a theorem OUTPUT and never a premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_InputSchedule
open Aeneas Aeneas.Std Result
open S2LeadInterface MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_NativeConsolidation S2W_AuthenticatedInputs
abbrev Observer := AdapterRw.LeadInputs.Observer

def observation {E : Type} (f : FirstCut) (s : SecondCut) (saved : alloc.vec.Vec U8)
    (nodes : Nat → Nat → Slice U8) (y1 : Slice U8)
    (pre middle : List (S2W_SiteSchedule.Event E))
    (fs : S2W_SiteSchedule.FirstSegments E) (ss : S2W_SiteSchedule.SecondSegments E)
    (before after : Site → Nat → Account) : Inputs Observer where
  reached := fun site => S2W_SiteSchedule.Event.site site ∈ S2W_SiteSchedule.timeline pre middle fs ss
  clock := S2W_SiteSchedule.clock pre middle fs ss
  proof := fun site => if site.rank ≤ 3 then f.proof else s.proof
  publicInput := fun site => if site.rank ≤ 3 then f.pub else s.pub
  proofAccount := fun site => if site.rank ≤ 3 then bytesOf f.raw.val else bytesOf s.raw.val
  checkpoint := fun site => if site = .save then alloc.vec.Vec.deref saved else s.checkpoint
  nodes := nodes
  y1 := y1
  observer := fun _ => none
  before := before
  after := after

/-- Exactly the twelve non-frame fields of the REVISED fourteen-field record.
No change to the full S2CallerFacts target or its account-frame obligations. -/
structure InputScheduleFacts (c : Inputs Observer) (ops : AdapterRw.Ops) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed) : Prop where
  proofBytes : ∀ site, c.reached site → bytesOf (c.proof site).val = stored
  publicBytes : ∀ site, c.reached site → bytesOf (c.publicInput site).val = pub
  proofSuffix : ∀ site, c.reached site → site = .tx1 ∨ site = .tx2 →
    c.proofAccount site = (c.proofAccount site).take 688 ++ stored
  proofLength : stored.length = 57607
  checkpointBytes : ∀ site, c.reached site → site = .save ∨ site = .tx2 ∨ site = .resume →
    bytesOf (c.checkpoint site).val = saved
  checkpointLength : saved.length = 1768
  nodeViews : ∀ b k, b < 2 → k < 3 → bytesOf (c.nodes b k).val =
    slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+k))
      (32*OraclePortSelectedDraft.capacity (3*b+k))
  y1Input : c.reached .tx1 → c.y1 = S8JoinFrozenScan.segment (c.proof .tx1) 7031 464
  observerNone : ∀ site, c.reached site → c.observer site = none
  reachedPrefix : ∀ a b, a.rank < b.rank → c.reached b → c.reached a
  callOrder : ∀ a b, a.rank < b.rank → c.reached a → c.reached b → c.clock a < c.clock b
  oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest ops) () H

/-- SourceCuts is used only as a locally computed intermediate. The native
entry theorem below computes it from the accepted pair; no theorem asks the
lead to trust this structure. -/
theorem input_schedule {E : Type} (ops : AdapterRw.Ops) (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (f : FirstCut) (s : SecondCut) (saved : alloc.vec.Vec U8)
    (cuts : SourceCuts ops accounts1 accounts2 saved f s)
    (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8)
    (writer : CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split)
    (reader : CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint)
    (version : CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
    (p2prime : P2Prime H f.proof f.pub s.proof s.pub)
    (entry : S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof)
    (multiproof : S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes)
    (scan : S2W_ChildJoins.S8StageConeJoin f.proof y1)
    (oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest ops) () H)
    (pre middle : List (S2W_SiteSchedule.Event E))
    (fs : S2W_SiteSchedule.FirstSegments E) (ss : S2W_SiteSchedule.SecondSegments E)
    (before after : Site → Nat → Account) :
    ∃ parsed, InputScheduleFacts (observation f s saved nodes y1 pre middle fs ss before after)
      ops H (bytesOf f.proof.val) (bytesOf f.pub.val) (bytesOf saved.val) parsed := by
  obtain ⟨proof,pub,cp,size,tr,parsed,parser,nodeViews,y1eq,_⟩ :=
    authenticated_geometry ops decode H f.semantic f.pub f.proof s.pub s.proof s.checkpoint
      y1 nodes f.split saved cuts.first cuts.second writer reader version p2prime entry multiproof scan
  refine ⟨parsed,⟨?_,?_,?_,cuts.proofLength,?_,size,nodeViews,?_,?_,?_,?_,oracle⟩⟩
  · intro site _
    change bytesOf (if site.rank ≤ 3 then f.proof else s.proof).val = _
    split <;> simp only [proof]
  · intro site _
    change bytesOf (if site.rank ≤ 3 then f.pub else s.pub).val = _
    split <;> simp only [pub]
  · intro site _ which
    rcases which with h | h <;> subst site
    · exact cuts.firstSuffix
    · exact cuts.secondSuffix.trans (congrArg (fun x => (bytesOf s.raw.val).take 688 ++ x) proof)
  · intro site _ which
    rcases which with h | h | h <;> subst site
    · rfl
    · exact cp
    · exact cp
  · intro _
    exact y1eq
  · intro _ _; rfl
  · intro a b _ _
    exact S2W_SiteSchedule.reached pre middle fs ss a
  · intro a b order _ _
    exact S2W_SiteSchedule.ordered pre middle fs ss a b order

/-- Derive every source-cut premise from the SAME accepted native owned pair,
then construct the twelve-field projection. Event exporter hypotheses belong
to the named child cones; their exact source trace equality is retained in the
conclusion as well. No conclusion-bearing whole-caller certificate is input. -/
theorem accepted_native_input_schedule {E : Type}
    (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_ExtractionBoundary.AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (runtime : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s, SourceCuts ops accounts1 accounts2 saved f s ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint →
      CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∀ (pre middle firstEvents secondEvents : List (S2W_SiteSchedule.Event E))
        (fs : S2W_SiteSchedule.FirstSegments E) (ss : S2W_SiteSchedule.SecondSegments E),
      S2W_SiteSchedule.FirstEntrySiteConeJoin firstEvents fs →
      S2W_SiteSchedule.SecondEntrySiteConeJoin secondEvents ss →
      ∀ (before after : Site → Nat → Account),
      ∃ parsed, InputScheduleFacts (observation f s saved nodes y1 pre middle fs ss before after)
          ops H (bytesOf f.proof.val) (bytesOf f.pub.val) (bytesOf saved.val) parsed ∧
        pre ++ [.site .tx1] ++ firstEvents ++ middle ++ [.site .tx2] ++ secondEvents =
          S2W_SiteSchedule.timeline pre middle fs ss := by
  obtain ⟨f,s,cuts⟩ := cuts_of_acceptance ops native1 native2 hashv extraction program accounts1 accounts2
    data1 data2 slot saved accepted1 accepted2
  refine ⟨f,s,cuts,?_⟩
  intro decode nodes y1 writer reader version p2prime entry multiproof scan
    pre middle firstEvents secondEvents fs ss firstSite secondSite before after
  obtain ⟨parsed,facts⟩ := input_schedule ops H accounts1 accounts2 f s saved cuts decode nodes y1
    writer reader version p2prime entry multiproof scan
    (S2W_ExtractionBoundary.native_oracle ops native1 native2 hashv extraction sha256 H p1 runtime)
    pre middle fs ss before after
  exact ⟨parsed,facts,by rw [firstSite.sourceTrace,secondSite.sourceTrace]; rfl⟩

#print axioms input_schedule
#print axioms accepted_native_input_schedule
#print InputScheduleFacts
end AspisR1.S2W_InputSchedule
end
