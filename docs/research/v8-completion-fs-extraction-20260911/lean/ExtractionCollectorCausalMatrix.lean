import ExtractionCollectorSuccessfulReplay
import ExtractionCollectorFinalMatrix
import SameBodyConsumeConstructsWord

/-!
# A response-compatible relation strategy constructed from successful cells

This leaf strengthens the earlier value-only matrix in one important way:
every matrix cell is itself a `SuccessfulReplay`, rather than an arbitrary
record placed in the collector's `.checked` constructor.  For each gamma row,
the four alpha continuations are assembled into one response-compatible
`SameBodyRelation.Strategy`.  The response before alpha is required to agree
across the four continuations; final256 and the later responses are selected
only after their legal challenge boundaries.

The source replay/fork theorem still has to construct `CompleteMatrix`, prove
that its cells share one chronological pre-alpha history, and produce
`AlphaPrefixCompatible`.  Equal parsed response0 values alone do not prove
that common-history fact.  This file does not assume terminal acceptance,
fold correctness, a quotient, or a payment witness.  Its endpoint is the
actual same-word `consume` success needed before any terminal or recovery
classification can be attached.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1200

namespace AspisV8Completion.ExtractionCollectorCausalMatrix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSQuerySchedule FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorSource ExtractionCollectorSuccessfulReplay
open ExtractionCollectorFinalMatrix
open SameBodyRelation SameBodyConsumeConstructsWord
open FSInterleavedSelectedIncrementBoundary

noncomputable section

abbrev K := FSNonzeroQM31.K
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position
abbrev Query := Fin 22 → Position
abbrev Bytes := List UInt8

variable {n m : Nat}
variable {z : Fin 10 → K} {cuts : FSBoundedTranscript.RootCuts}
variable {initialDigest : Block}
variable {firstWork : Point → Script Bytes Block Unit n}
variable {secondWork : Point → Point → Script Bytes Block Unit m}

structure Cell (n m : Nat) (z : Fin 10 → K)
    (cuts : FSBoundedTranscript.RootCuts) (initialDigest : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    extends SuccessfulReplay z cuts initialDigest firstWork secondWork

local notation "CurrentCell" =>
  Cell n m z cuts initialDigest firstWork secondWork

include n m z cuts initialDigest firstWork secondWork

def gammaOf (cell : CurrentCell) : K := cell.record.gamma
def alphaOf (cell : CurrentCell) : K := cell.record.middle.middle.alpha0
def kappaOf (cell : CurrentCell) : K := cell.record.middle.middle.kappa
def tauOf (cell : CurrentCell) : K := cell.record.middle.middle.tau
def rhoOf (cell : CurrentCell) : K := cell.record.middle.middle.rho

/-- The q22 schedule certificate is derived from the successful execution of
`suffixContinuation`; it is not a field of a proposed replay record. -/
structure QueryEvidence (cell : CurrentCell) : Prop where
  valid : ValidAccepted cell.record.middle.middle.queries
  count : cell.record.middle.middle.queries.length = 22

theorem query_evidence (cell : CurrentCell) : QueryEvidence cell := by
  obtain ⟨staged, middleDigest, _prefix, suffix⟩ :=
    successful_wholeStaged_components firstWork secondWork z cuts cell.body
      initialDigest cell.tape cell.oracle cell.record cell.finalDigest cell.success
  unfold suffixContinuation at suffix
  by_cases h : ValidAccepted staged.middle.middle.queries ∧
      staged.middle.middle.queries.length = 22
  · rw [dif_pos h, run_bind] at suffix
    cases suffixRun :
        (run cell.tape
          (interleavedSelectedSuffix cuts
            (scheduleOf staged.middle.middle.queries h.1 h.2).positions cell.body
            middleDigest staged.middle.functional.data staged.middle.middle.alpha0
            staged.middle.middle.rho)
          (run cell.tape
            (prefixMiddleScript firstWork secondWork z cell.body initialDigest)
            cell.oracle).2).1 with
    | none => simp [suffixRun] at suffix
    | some value =>
      rcases value with ⟨result, resultDigest⟩
      cases result with
      | error e => simp [suffixRun, run] at suffix
      | ok output =>
        simp only [suffixRun, run] at suffix
        have pairEq := Option.some.inj suffix
        have recordEq := Except.ok.inj (congrArg Prod.fst pairEq)
        have queriesEq := congrArg
          (fun returned : Record cell.body z => returned.middle.middle.queries)
          recordEq
        constructor
        · rw [← queriesEq]
          exact h.1
        · rw [← queriesEq]
          exact h.2
  · rw [dif_neg h] at suffix
    simp [run] at suffix

def queryOf (cell : CurrentCell) : Query :=
  (scheduleOf cell.record.middle.middle.queries
    (query_evidence cell).valid (query_evidence cell).count).positions

def coinsOf (cell : CurrentCell) : Fin 3 → K
  | ⟨0, _⟩ => cell.record.suffix.alpha1
  | ⟨1, _⟩ => cell.record.suffix.alpha2
  | ⟨2, _⟩ => cell.record.suffix.alpha3

noncomputable def wordOf (cell : CurrentCell) : Word K :=
  SameBodyFunctionalProducerSource.wordOfValues
    (Classical.choose (parser_values cell.record))

def responseOf (cell : CurrentCell) (round : Fin 4) : Sent K :=
  response (wordOf cell) round

def finalOf (cell : CurrentCell) : Final K := finalValues (wordOf cell)

/-- A three-round continuation whose messages are the canonical fields of
this cell.  Each message is returned at its legal boundary; the unused
continuations are deliberately constant rather than inspecting future
coins. -/
def tailOf (cell : CurrentCell) : Tail K 3 :=
  .round (responseOf cell 1) fun _ =>
    .round (responseOf cell 2) fun _ =>
      .round (responseOf cell 3) fun _ => .done

theorem tailOf_messages (cell : CurrentCell) :
    tailMessages (tailOf cell) (coinsOf cell) = laterResponses (wordOf cell) := by
  rfl

abbrev Outcomes (Record RejectReason ResourceReason : Type*) :=
  List (AttemptOutcome Record RejectReason ResourceReason)

abbrev CurrentComplete (RejectReason ResourceReason : Type*)
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason) :=
  CompleteMatrix
    (Record := CurrentCell)
    (RejectReason := RejectReason)
    (ResourceReason := ResourceReason)
    (@gammaOf n m z cuts initialDigest firstWork secondWork)
    (@alphaOf n m z cuts initialDigest firstWork secondWork)
    labels outcomes

/-- The response compatibility needed to assemble the four alpha cells of a
row.  Kappa, tau and response0 agree as values.  These equalities do not by
themselves establish a shared chronological oracle/source prefix; that is a
separate producer obligation. -/
structure AlphaPrefixCompatible
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes) : Prop where
  kappa_eq : ∀ row column,
    kappaOf (complete.matrix row column) = kappaOf (complete.matrix row 0)
  tau_eq : ∀ row column,
    tauOf (complete.matrix row column) = tauOf (complete.matrix row 0)
  response0_eq : ∀ row column,
    responseOf (complete.matrix row column) 0 =
      responseOf (complete.matrix row 0) 0

/-- Unique lookup of an alpha-labelled cell.  Outside the four scheduled
labels it uses column zero; no theorem relies on that default. -/
def columnAt (labels : MatrixLabels K K) (row : Fin 29) (alpha : K) : Fin 4 :=
  if h : ∃ column, labels.alpha row column = alpha then Classical.choose h else 0

theorem columnAt_label (labels : MatrixLabels K K)
    (row : Fin 29) (column : Fin 4) :
    columnAt labels row (labels.alpha row column) = column := by
  classical
  unfold columnAt
  split
  next h =>
    apply labels.alpha_injective row
    exact Classical.choose_spec h
  next h => exact (h ⟨column, rfl⟩).elim

def selectedCell {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (row : Fin 29) (alpha : K) : CurrentCell :=
  complete.matrix row (columnAt labels row alpha)

theorem selectedCell_at_label {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    selectedCell labels outcomes complete row (labels.alpha row column) =
      complete.matrix row column := by
  unfold selectedCell
  rw [columnAt_label (n := n) (m := m) (z := z) (cuts := cuts)
    (initialDigest := initialDigest) (firstWork := firstWork)
    (secondWork := secondWork) labels row column]

/-- One response-compatible relation strategy for the four alpha cells of a
fixed gamma row.  The pre-alpha response is shared.  Final and later messages
are looked up only after alpha is supplied.  A separate source theorem must
show these cells are continuations of one actual pre-alpha history. -/
def rowStrategy {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (row : Fin 29) : Strategy K Query := fun _tau =>
  { response0 := responseOf (complete.matrix row 0) 0
    afterAlpha0 := fun alpha =>
      let cell := selectedCell labels outcomes complete row alpha
      { final256 := finalOf cell
        afterQueries := fun _query _rho => tailOf cell } }

theorem rowStrategy_response0
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (compatible : AlphaPrefixCompatible labels outcomes complete)
    (row : Fin 29) (column : Fin 4) :
    (rowStrategy labels outcomes complete row
      (tauOf (complete.matrix row column))).response0 =
        responseOf (complete.matrix row column) 0 := by
  exact (compatible.response0_eq row column).symm

theorem rowStrategy_final
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    ((rowStrategy labels outcomes complete row
      (tauOf (complete.matrix row column))).afterAlpha0
        (labels.alpha row column)).final256 =
      finalOf (complete.matrix row column) := by
  simp [rowStrategy, selectedCell_at_label]

theorem rowStrategy_tail
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (row : Fin 29) (column : Fin 4) :
    (((rowStrategy labels outcomes complete row
      (tauOf (complete.matrix row column))).afterAlpha0
        (labels.alpha row column)).afterQueries
          (queryOf (complete.matrix row column))
          (rhoOf (complete.matrix row column))) =
      tailOf (complete.matrix row column) := by
  simp [rowStrategy, selectedCell_at_label]

/-- The complete matrix and its response compatibility construct same-word
consumer success at every cell.  No `consume = some _`, serialized-word
equality, final equality, or later-response equality is an input. -/
theorem row_consume_succeeds
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (compatible : AlphaPrefixCompatible labels outcomes complete)
    (row : Fin 29) (column : Fin 4)
    (ops : Arithmetic K) (ordinary : K)
    (increment : Final K → Query → K → K) :
    ∃ result, consume ops (rowStrategy labels outcomes complete row)
      (wordOf (complete.matrix row column))
      (tauOf (complete.matrix row column)) (labels.alpha row column)
      (queryOf (complete.matrix row column)) (rhoOf (complete.matrix row column))
      (coinsOf (complete.matrix row column)) ordinary increment = some result := by
  let cell := complete.matrix row column
  have first := rowStrategy_response0 labels outcomes complete compatible row column
  have final := rowStrategy_final labels outcomes complete row column
  have tail := rowStrategy_tail labels outcomes complete row column
  simp [consume, first, final, tail, responseOf, finalOf, tailOf_messages]

/-- Consequently each selected body is the realised serialization of the
response-compatible row strategy.  The separate chronological replay theorem
must still show that this strategy is induced by one common pre-alpha source
history rather than merely agreeing with the selected cells. -/
theorem row_serialized_word
    {RejectReason ResourceReason : Type*}
    (labels : MatrixLabels K K)
    (outcomes : Outcomes CurrentCell RejectReason ResourceReason)
    (complete : CurrentComplete RejectReason ResourceReason labels outcomes)
    (compatible : AlphaPrefixCompatible labels outcomes complete)
    (row : Fin 29) (column : Fin 4)
    (ops : Arithmetic K) (ordinary : K)
    (increment : Final K → Query → K → K) :
    wordOf (complete.matrix row column) =
      produce (SameBodyAssembly.early (wordOf (complete.matrix row column)))
        (rowStrategy labels outcomes complete row)
        (tauOf (complete.matrix row column)) (labels.alpha row column)
        (queryOf (complete.matrix row column)) (rhoOf (complete.matrix row column))
        (coinsOf (complete.matrix row column)) := by
  obtain ⟨result, consumed⟩ := row_consume_succeeds labels outcomes complete
    compatible row column ops ordinary increment
  exact consume_success_constructs_word ops
    (rowStrategy labels outcomes complete row)
    (wordOf (complete.matrix row column))
    (tauOf (complete.matrix row column)) (labels.alpha row column)
    (queryOf (complete.matrix row column)) (rhoOf (complete.matrix row column))
    (coinsOf (complete.matrix row column)) ordinary increment result consumed

#print axioms query_evidence
#print axioms tailOf_messages
#print axioms columnAt_label
#print axioms selectedCell_at_label
#print axioms rowStrategy_response0
#print axioms rowStrategy_final
#print axioms rowStrategy_tail
#print axioms row_consume_succeeds
#print axioms row_serialized_word

end
end AspisV8Completion.ExtractionCollectorCausalMatrix
