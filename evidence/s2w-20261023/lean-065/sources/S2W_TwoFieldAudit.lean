import S2W_ChildEventPorts

/-! Exact remaining fields, not a new closure assumption. This audit cannot
be used as a native S2CallerFacts proof until the two source frame obligations
are proved on the SAME account before/after observations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_TwoFieldAudit
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2LeadInterface S2W_InputSchedule

/-- The partial record has exactly the other twelve field types. This
 equivalence is an audit, not discharge of either remaining conjunct. -/
theorem full_fields_iff (c : Inputs Observer) (ops : AdapterRw.Ops) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (partialFacts : InputScheduleFacts c ops H stored pub saved parsed) :
    S2W_LeadInterface.S2CallerFacts c (S2Z.Oracle.leadDigest ops) () H stored pub saved parsed ↔
      (∀ site, c.reached site → ∀ account, dataWrite site account = false →
        c.after site account = c.before site account) ∧
      (c.reached .tx1 → {c.after .tx1 2 with data := (c.before .tx1 2).data} = c.before .tx1 2) := by
  constructor
  · intro facts
    exact ⟨facts.accountFrame,facts.writtenMetadata⟩
  · rintro ⟨frame,metadata⟩
    exact {
      proofBytes := partialFacts.proofBytes
      publicBytes := partialFacts.publicBytes
      proofSuffix := partialFacts.proofSuffix
      proofLength := partialFacts.proofLength
      checkpointBytes := partialFacts.checkpointBytes
      checkpointLength := partialFacts.checkpointLength
      nodeViews := partialFacts.nodeViews
      y1Input := partialFacts.y1Input
      observerNone := partialFacts.observerNone
      reachedPrefix := partialFacts.reachedPrefix
      callOrder := partialFacts.callOrder
      accountFrame := frame
      writtenMetadata := metadata
      oracle := partialFacts.oracle }

/-- Source-observation independence check only, NOT a native execution
counterexample. Arbitrary observed account effects can falsify BOTH fields;
none of the twelve input/schedule fields restricts these account functions.
Do not silently define native after-accounts to a logical commit spec. -/
theorem changed_metadata_excludes_facts {E : Type}
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (saved : alloc.vec.Vec U8) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8)
    (pre middle : List (S2W_SiteSchedule.Event E))
    (fs : S2W_SiteSchedule.FirstSegments E) (ss : S2W_SiteSchedule.SecondSegments E)
    (account : Account) (ops : AdapterRw.Ops) (H : Bytes → State)
    (stored pub savedBytes : Bytes) (parsed : Parsed) :
    let changed := {account with key := 0 :: account.key}
    let c := observation f s saved nodes y1 pre middle fs ss (fun _ _ => account) (fun _ _ => changed)
    ¬ (∀ site, c.reached site → ∀ a, dataWrite site a = false → c.after site a = c.before site a) ∧
    ¬ (c.reached .tx1 → {c.after .tx1 2 with data := (c.before .tx1 2).data} = c.before .tx1 2) ∧
    ¬ S2W_LeadInterface.S2CallerFacts c (S2Z.Oracle.leadDigest ops) () H stored pub savedBytes parsed := by
  dsimp only
  have reached1 : (observation f s saved nodes y1 pre middle fs ss (fun _ _ => account)
      (fun _ _ => {account with key := 0 :: account.key})).reached .tx1 :=
    S2W_SiteSchedule.reached pre middle fs ss .tx1
  have changed : {account with key := 0 :: account.key} ≠ account := by
    intro eq
    have lengths := congrArg (fun a : Account => a.key.length) eq
    simp only [List.length_cons] at lengths
    omega
  have frame : ¬ (∀ site,
      (observation f s saved nodes y1 pre middle fs ss (fun _ _ => account)
        (fun _ _ => {account with key := 0 :: account.key})).reached site →
      ∀ a, dataWrite site a = false →
        {account with key := 0 :: account.key} = account) := by
    intro h
    exact changed (h .tx1 reached1 0 rfl)
  have metadata : ¬ ((observation f s saved nodes y1 pre middle fs ss (fun _ _ => account)
      (fun _ _ => {account with key := 0 :: account.key})).reached .tx1 →
      {{account with key := 0 :: account.key} with data := account.data} = account) := by
    intro h
    exact changed (h reached1)
  refine ⟨frame,metadata,?_⟩
  intro facts
  exact frame facts.accountFrame

#print axioms full_fields_iff
#print axioms changed_metadata_excludes_facts
#print axioms S2W_ExtractionBoundary.accepted_native_observation
#print axioms S2W_ExtractionBoundary.native_oracle
#print axioms S2W_NativeConsolidation.accepted_native_consolidation
#print axioms S2W_ChildEventPorts.accepted_native_observed_inputs
end AspisR1.S2W_TwoFieldAudit
end
