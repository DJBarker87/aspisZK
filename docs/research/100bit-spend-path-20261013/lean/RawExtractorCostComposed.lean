import RawExtractorCostLedger
import RawChecksAdaptiveFailureNoModel

/-! Conditional M10 composition for the exact experiment used by the M9
no-model theorem. Scheduling, implementation overhead, log reconstruction and
bit-cost refinement are named premises, not consequences of partial mirrors. -/
noncomputable section
namespace AspisR1.RawExtractorCostComposed
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutWordsFromView
open AspisR1.RawCutTranscriptRun
open AspisR1.RawAdaptiveDecoderInjection
open AspisR1.RawAdaptiveLiteralDecoder
open AspisR1.RawAdaptiveClassifierHitDensity
open AspisR1.DecodedFirstReadUnionBound
open AspisR1.GenericNoHit
open AspisR1.RawRecordedOracleExtractionMass
open AspisR1.RawRecordedActualAdaptiveFailureBound

open AspisV8R19.OracleResampling
open AspisR1.RawExtractorCostLedger

abbrev Coins := GSConcreteByteDecoderBank.RawCoins
abbrev K := AspisWideTower.WideExact

structure Resources where
  fieldOps : Nat
  logReads : Nat
  bits : Nat

def Resources.total (r : Resources) : Nat := r.fieldOps + r.logReads + r.bits

/-- The projection must refine the ordinary run-and-private-coins extractor.
Cost adequacy still needs LedgerRefinement; output equality alone cannot
certify an implementation's costs. -/
structure CostedExtractor where
  eval : RunView → Coins → Option SpendRelation.Wspend × Resources
  value : ∀ run coins, (eval run coins).1 =
    RawRecordedPublicSpendExtractor.extract run coins

structure Parameters where
  n : Nat -- maximum stored polynomial size and word-reconstruction count
  logSize : Nat -- actual recorded-log length bound (not merely verifier Q)
  listSize : Nat
  b : Nat -- exponent/field representation bit bound
  calls : Nat
  depth : Nat
  ell : Nat
  retries : Nat
  overheadConstant : Nat
  overheadDegree : Nat

def Parameters.count (p : Parameters) : Nat :=
  p.calls * (p.depth*p.ell+1) * (p.retries+1) * (p.ell+1)

def Parameters.overhead (p : Parameters) : Nat :=
  p.overheadConstant * (p.n+p.logSize+p.listSize+p.b+1)^p.overheadDegree

/-- Conservative polynomial supplied to the modular-multiply implementation
bridge. Power count alone does not establish this field-operation budget. -/
def Parameters.mulBudget (p : Parameters) : Nat :=
  p.n*p.n + (2*p.n+1)*(100*(2*p.n+5)*(2*p.n+5))

def Parameters.fieldBudget (p : Parameters) : Nat :=
  p.count*gcdBudget p.n + p.count*divisionBudget p.n +
    (p.count*(2*p.b))*p.mulBudget + p.overhead

def Parameters.readBudget (p : Parameters) : Nat := 7*p.n*p.logSize

def Parameters.attemptBudget (p : Parameters) : Nat :=
  p.fieldBudget + p.readBudget +
    (p.fieldBudget+p.readBudget+p.overhead)*(p.b+1)^2

/-- Missing implementation-level premises, deliberately exposed for C3.
`jobs` must enumerate every arithmetic call, including failed retries.
`bounded_jobs` must cover normalization, interpolation, list filters,
merge, final witness checking, sampler, and modular-multiplication work.
`reads` must link actual recorded-log reconstruction to the finite-log model.
`bit_accounting` must cover all allocation, parsing and arithmetic bit work.
These premises assert adequacy of the cost model, beyond value refinement. -/
structure LedgerRefinement (e : CostedExtractor) (p : Parameters) : Prop where
  bounded_jobs : ∀ run coins, run.2.2 = true →
    ∃ jobs : Jobs K, jobs.Bounded p.n p.b p.count ∧
      (e.eval run coins).2.fieldOps ≤ jobs.charge p.mulBudget + p.overhead
  reads : ∀ run coins, run.2.2 = true →
    (e.eval run coins).2.logReads ≤ p.readBudget
  bit_accounting : ∀ run coins, run.2.2 = true →
    (e.eval run coins).2.bits ≤
      ((e.eval run coins).2.fieldOps + (e.eval run coins).2.logReads +
        p.overhead)*(p.b+1)^2

/-- All finite private tapes, including aborts, satisfy a deterministic bound;
therefore their uniform mean does too. No geometric-retry assumption is used. -/
theorem accepted_attempt_cost (e : CostedExtractor) (p : Parameters)
    (h : LedgerRefinement e p) (run : RunView) (ha : run.2.2 = true) :
    (∀ coins, (e.eval run coins).2.total ≤ p.attemptBudget) ∧
    mean (fun coins : Coins => ((e.eval run coins).2.total : ℚ)) ≤
      (p.attemptBudget : ℚ) := by
  have hall (coins : Coins) : (e.eval run coins).2.total ≤ p.attemptBudget := by
    obtain ⟨jobs, hj, hf⟩ := h.bounded_jobs run coins ha
    have hf' : (e.eval run coins).2.fieldOps ≤ p.fieldBudget :=
      hf.trans (Nat.add_le_add_right (jobs_charge_le jobs p.n p.b p.count p.mulBudget hj) _)
    have hr := h.reads run coins ha
    have hb := (h.bit_accounting run coins ha).trans
      (Nat.mul_le_mul_right ((p.b+1)^2)
        (Nat.add_le_add_right (Nat.add_le_add hf' hr) p.overhead))
    exact Nat.add_le_add (Nat.add_le_add hf' hr) hb
  refine ⟨hall, ?_⟩
  calc
    _ ≤ mean (fun _ : Coins => (p.attemptBudget : ℚ)) := mean_mono (by
      intro coins
      exact_mod_cast hall coins)
    _ = _ := mean_const _

/-- Whole recorded-run conditional D3 cost/safety/failure contract. The
collision and decoded-start terms remain in the ledger; deltaE is only the
existing bank-abort allowance, not a claim about conditional success on every
accepted transcript. Fix overheadConstant/overheadDegree uniformly across a
parameter family to obtain a polynomial family. -/
theorem recorded_extractor_cost_and_failure
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q N : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (experiment P (verifier decoder d))).1 ≤ Q)
    (htag : ∀ H : Bytes → State,
      (eval H (experiment P (verifier decoder d))).2.1.1.tag = 2)
    (hchecks : ∀ H : Bytes → State,
      FS2.accepts (eval H (experiment P (verifier decoder d))) →
      LiteralAcceptanceTerminal.Checks
        (eval H (experiment
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
          (verifier decoder d))).2.1.1
        (((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.2 33).rounds))
    (hN : ∀ H : Bytes → State, decoderFirstReads
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoice.choose) emptyTable
      (eval H (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))).1 ≤ N)
    (e : CostedExtractor) (p : Parameters) (hcost : LedgerRefinement e p) :
    (∀ H : Bytes → State,
      let run := eval H (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d))
      run.2.2 = true →
        mean (fun coins : Coins => ((e.eval run coins).2.total : ℚ)) ≤
          (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 ≤ 1 / (2 : ℚ)^120) ∧
    lazyMean
      (AcceptedAdaptiveFiatShamir.experiment
        (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
        (verifier decoder d)) emptyTable failureMass ≤
      kappa Q + (N : ℚ)*PerAttemptEnvelope.B + (1 / (2 : ℚ)^126) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H ha
    exact (accepted_attempt_cost e p hcost _ ha).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractor.returned_relation run coins w
      ((e.value run coins).symm.trans hw)
  · norm_num
  · exact RawChecksAdaptiveFailureNoModel.checked_acceptance_failure_bound_no_model
      decoder d P Q N hQ htag hchecks hN

#print axioms accepted_attempt_cost
#print axioms recorded_extractor_cost_and_failure
end AspisR1.RawExtractorCostComposed
end
