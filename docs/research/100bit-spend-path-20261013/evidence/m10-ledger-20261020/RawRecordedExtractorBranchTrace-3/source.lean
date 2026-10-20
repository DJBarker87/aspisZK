import RawExtractorCostComposedV2

/-! Branch instrumentation of the existing parser/bank/candidate caller.
These are call events, not field/bit/read costs of their implementations.
Generic Option lemmas keep the large concrete decoder opaque. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.RawRecordedExtractorBranchTrace
open RawCutWordsFromRunExecutable RawCutWordsFromRunPublicValid

inductive Event where
  | parsePublic
  | decoderBank
  | candidateScan

/-- Record one caller event and the events of its successful continuation. -/
def bindTrace {A B : Type} (input : Option A) (event : Event)
    (next : A → Option B × List Event) : Option B × List Event :=
  match input with
  | none => (none, [event])
  | some a => let r := next a; (r.1, event :: r.2)

theorem bindTrace_value {A B : Type} (input : Option A) (event : Event)
    (next : A → Option B × List Event) :
    (bindTrace input event next).1 = input.bind (fun a => (next a).1) := by
  cases input <;> rfl

theorem bindTrace_length {A B : Type} (input : Option A) (event : Event)
    (next : A → Option B × List Event) (n : Nat)
    (h : ∀ a, (next a).2.length ≤ n) :
    (bindTrace input event next).2.length ≤ n + 1 := by
  cases input with
  | none => change 1 ≤ n + 1; omega
  | some a => exact Nat.add_le_add_right (h a) 1

theorem two_bind_value {A B C : Type}
    (input : Option A) (middle : Option B) (next : A → B → Option C)
    (e1 e2 e3 : Event) :
    (bindTrace input e1 (fun a => bindTrace middle e2
      (fun b => (next a b, [e3])))).1 =
      input.bind (fun a => middle.bind (next a)) := by
  cases input <;> cases middle <;> rfl

theorem two_bind_length {A B C : Type}
    (input : Option A) (middle : Option B) (next : A → B → Option C)
    (e1 e2 e3 : Event) :
    (bindTrace input e1 (fun a => bindTrace middle e2
      (fun b => (next a b, [e3])))).2.length ≤ 3 := by
  cases input <;> cases middle <;> decide

attribute [local irreducible] runDecodedPublic
  GSConcreteByteDecoderBank.run LiteralComputedCandidateExtract.extract
  initialWordsFromRun finalWordFromRun
  AspisWide.GSConcreteReceivedWordInputs.fromWords

/-- Same calls and short-circuit branches as the actual extractor. -/
def extract (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    Option SpendRelation.Wspend × List Event :=
  bindTrace (runDecodedPublic run) .parsePublic fun pub =>
    let W := initialWordsFromRun run
    let V := fun _ => finalWordFromRun run
    bindTrace (GSConcreteByteDecoderBank.run
      (AspisWide.GSConcreteReceivedWordInputs.fromWords W V) coins) .decoderBank
      fun out => (LiteralComputedCandidateExtract.extract pub W
        (GSByteJointSpendExtractor.decodedLists W out), [.candidateScan])

#check extract

theorem value (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    (extract run coins).1 = RawRecordedPublicSpendExtractor.extract run coins := by
  change (bindTrace (runDecodedPublic run) .parsePublic (fun pub =>
    bindTrace (GSConcreteByteDecoderBank.run
      (AspisWide.GSConcreteReceivedWordInputs.fromWords
        (initialWordsFromRun run) (fun _ => finalWordFromRun run)) coins) .decoderBank
      (fun out => (LiteralComputedCandidateExtract.extract pub (initialWordsFromRun run)
        (GSByteJointSpendExtractor.decodedLists (initialWordsFromRun run) out),
        [.candidateScan])))).1 =
    (runDecodedPublic run).bind (fun pub =>
      (GSConcreteByteDecoderBank.run
        (AspisWide.GSConcreteReceivedWordInputs.fromWords
          (initialWordsFromRun run) (fun _ => finalWordFromRun run)) coins).bind
        (fun out => LiteralComputedCandidateExtract.extract pub (initialWordsFromRun run)
          (GSByteJointSpendExtractor.decodedLists (initialWordsFromRun run) out)))
  exact two_bind_value _ _ _ _ _ _

/-- At most one parse, one bank call and one candidate call; this says
nothing about the number of operations inside those calls. -/
theorem event_count (run : RawCutProverCompiler.RunView)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    (extract run coins).2.length ≤ 3 :=
  two_bind_length _ _ _ _ _ _

/-- Output equality is independent of the resource implementation. No default
resource labels and no ledger instance are supplied by this construction. -/
def attachResources
    (resources : RawCutProverCompiler.RunView → GSConcreteByteDecoderBank.RawCoins →
      RawExtractorCostComposedV2.Resources) : RawExtractorCostComposedV2.CostedExtractor where
  eval run coins := ((extract run coins).1, resources run coins)
  value := value

theorem attachResources_value
    (resources : RawCutProverCompiler.RunView → GSConcreteByteDecoderBank.RawCoins →
      RawExtractorCostComposedV2.Resources)
    (run : RawCutProverCompiler.RunView) (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((attachResources resources).eval run coins).1 =
      RawRecordedPublicSpendExtractor.extract run coins :=
  (attachResources resources).value run coins

#print axioms bindTrace_value
#print axioms bindTrace_length
#print axioms two_bind_value
#print axioms two_bind_length
#print axioms value
#print axioms event_count
#print axioms attachResources_value
end AspisR1.RawRecordedExtractorBranchTrace
