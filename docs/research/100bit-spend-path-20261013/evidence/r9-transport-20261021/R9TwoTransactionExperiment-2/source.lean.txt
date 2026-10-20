import RawDigestLogCarrier
import RawRecordedOracleExtractionMass
import OracleProgramLawExt
import QueryScanAbortAccounting
import QueryScanModelFailure

/-! Extraction-independent source experiment. The stage-1 result retains the
completed (possibly ghost-padded) query tape, even on rejection. A checkpoint
is passed directly to stage 2 under the same memoized byte oracle. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R9TwoTransactionExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMass
attribute [local instance] Classical.propDecidable

abbrev WordTape := Fin 64 → Fin (2^18)
abbrev Run := RawCutProverCompiler.RunView

structure First (C : Type) where
  checkpoint : Option C
  words : WordTape

structure Outcome (C : Type) where
  first : First C
  /-- Source acceptance/public/messages and its designated recorded log. -/
  resumed : Option Run

/-- Rejection is explicit. There is no restart, oracle reset or conditioning
on either transaction succeeding. Source calls outside the recorded core
remain in the enclosing interpreter trace. -/
def experiment {C : Type} (tx1 : Program Bytes State (First C))
    (tx2 : C → Program Bytes State Run) : Program Bytes State (Outcome C) :=
  bind tx1 fun first =>
    match first.checkpoint with
    | none => .done ⟨first, none⟩
    | some c => bind (tx2 c) fun run => .done ⟨first, some run⟩

/-- The event includes independent private extractor coins. A successful
stage 2 is reachable only through the checkpoint produced by stage 1. -/
def failure {C : Type} (v : View Bytes State (Outcome C))
    (coins : GSConcreteByteDecoderBank.RawCoins) : Prop :=
  ∃ run, v.2.resumed = some run ∧ run.2.2 = true ∧
    RawRecordedPublicSpendExtractor.extract run coins = none

def deployedMass {C : Type} (v : View Bytes State (Outcome C)) : ℚ :=
  mean (fun coins => indicator (failure v coins))

def abort {C : Type} (v : View Bytes State (Outcome C)) : Prop :=
  QueryScanModelFailure.fails v.2.first.words

/-- Chronological concatenation, unlike the R10 inventory union. -/
theorem eval_success {C : Type} (tx1 : Program Bytes State (First C))
    (tx2 : C → Program Bytes State Run) (H : Bytes → State)
    (c : C) (hc : (eval H tx1).2.checkpoint = some c) :
    eval H (experiment tx1 tx2) =
      ((eval H tx1).1 ++ (eval H (tx2 c)).1,
        ⟨(eval H tx1).2, some (eval H (tx2 c)).2⟩) := by
  simp [experiment, eval_bind, hc, eval]

/-- Common certificate handoff from LOG-TX2: instantiate h1/h2 and coverage
with the separately checked tx1/tx2 embedding results. No generated packages
are imported together and no chronology follows from these certificates. -/
theorem joint_inventory (H : Bytes → State) (tr1 tr2 : List (Bytes × State))
    (reached1 reached2 : Bytes × State → Prop)
    (h1 : AspisR1DigestLogCarrier.Consistent H tr1) (h2 : AspisR1DigestLogCarrier.Consistent H tr2)
    (cover1 : AspisR1DigestLogCarrier.Covers reached1 tr1) (cover2 : AspisR1DigestLogCarrier.Covers reached2 tr2) :
    AspisR1DigestLogCarrier.Consistent H (tr1 ++ tr2) ∧
      AspisR1DigestLogCarrier.Covers (fun q => reached1 q ∨ reached2 q) (tr1 ++ tr2) :=
  ⟨AspisR1DigestLogCarrier.append_consistent H tr1 tr2 h1 h2,
    AspisR1DigestLogCarrier.append_covers reached1 reached2 tr1 tr2 cover1 cover2⟩

/-- This is a source *run* refinement, not a mass inequality: it preserves
acceptance, exact public statement, messages and the extractor's recorded
log. Inventory containment alone cannot establish it (R9/R10/R16/R20). -/
def OrderedSourceRefinement {C : Type} (source : Program Bytes State (Outcome C))
    (model : Experiment) : Prop :=
  ∀ H : Bytes → State, ¬ abort (eval H source) →
    ∀ run, (eval H source).2.resumed = some run → run = eval H model

/-- The generic QueryScan transfer rule, applied for each extractor tape.
No equality or inequality of failure probabilities is assumed. -/
theorem pointwise_transfer {C : Type} (source : Program Bytes State (Outcome C))
    (model : Experiment) (hrefine : OrderedSourceRefinement source model)
    (H : Bytes → State) :
    deployedMass (eval H source) ≤ failureMass (eval H model) +
      indicator (abort (eval H source)) := by
  have hi := QueryScanAbortAccounting.transfer
    (failure (eval H source))
    (fun coins => (eval H model).2.2 = true ∧
      RawRecordedPublicSpendExtractor.extract (eval H model) coins = none)
    (fun _ => abort (eval H source)) (by
      intro coins hs
      by_cases ha : abort (eval H source)
      · exact Or.inr ha
      · obtain ⟨run, hr, haccept, hfail⟩ := hs
        have he := hrefine H ha run hr
        exact Or.inl (by simpa only [he] using And.intro haccept hfail))
  change deployedMass (eval H source) ≤ failureMass (eval H model) + _ at hi
  change deployedMass (eval H source) ≤ failureMass (eval H model) +
    mean (fun _ : GSConcreteByteDecoderBank.RawCoins => indicator (abort (eval H source))) at hi
  rw [mean_const] at hi
  exact hi

#print axioms eval_success
#print axioms joint_inventory
#print axioms pointwise_transfer
end AspisR1.R9TwoTransactionExperiment
end
