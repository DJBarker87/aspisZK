import SameBodyChronologicalPreparedScalar
import SameBodyLiveRelationObservation
import SameBodyTerminalExecution

/-!
# Constructed authenticated scalar through the relation terminal

This leaf executes the pure relation consumer and terminal Boolean after a
same-body `Ready` observation and constructed chronological authentication
facts exist. The exact remaining source producer is isolated below.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1000

namespace AspisV8Completion.SameBodyChronologicalRelationTerminal

open SameBodyRelation SameBodyTerminalExecution
open SameBodyLiveRelationObservation SameBodyChronologicalPreparedScalar
open SameBodyAuthenticatedIncrement SameBodyLiveTerminalInput
open SameBodyQueryClaimExact
open AspisV8.OptimizedRelationRefinement
open AspisV8.SelectedReceivedOracle
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor

abbrev K := SameBodyAuthenticatedIncrement.K
abbrev Query := Fin 22 → AspisPool.V7MerkleQueryExtractor.Position

noncomputable section

local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero

theorem quarter_exact : (1 / 4 : K) * 4 = 1 := by
  have h4 : (4 : K) ≠ 0 := by
    intro h
    have product : (2 : K) * 2 = 0 := by norm_num at h ⊢; exact h
    rcases mul_eq_zero.mp product with h2 | h2
    · exact (NeZero.ne (2 : K)) h2
    · exact (NeZero.ne (2 : K)) h2
  simpa [one_div] using inverse_quarter_exact h4

/-- The remaining pre-tau/source-arithmetic producer. `causalWord` connects
the canonical same-body parser output to one causal strategy fixed at the
pre-tau boundary; it is not a terminal-success premise. -/
structure SourceRelationProducer {view : RawHashInput → Digest208}
    (ready : Ready view) where
  early : Fin 417 → K
  strategy : Strategy K Query
  ordinary : K
  terminalWeight : Fin 256 → K
  causalWord : ready.input.word = produce early strategy ready.middle.tau
    ready.middle.alpha0 ready.prepared.query ready.middle.rho ready.input.coins

def initialClaim {view : RawHashInput → Digest208} (ready : Ready view)
    (source : SourceRelationProducer ready) : K :=
  let ops := (ringArithmetic (1 / 4 : K)).toArithmetic
  let first := source.strategy ready.middle.tau
  let afterFirst := ops.evaluate7 (compact ops source.ordinary first.response0)
    ready.middle.alpha0
  ops.sub afterFirst (ready.prepared.relationIncrement ready.input.final256
    ready.prepared.query ready.middle.rho)

def terminalCheck {view : RawHashInput → Digest208} (ready : Ready view)
    (source : SourceRelationProducer ready) : Bool :=
  check (1 / 4 : K) ready.input.word source.terminalWeight
    (initialClaim ready source) ready.input.coins

/-- Consumer success is derived by execution from the causal word. -/
theorem consume_is_some {view : RawHashInput → Digest208}
    (ready : Ready view) (source : SourceRelationProducer ready) :
    (consume (ringArithmetic (1 / 4 : K)).toArithmetic source.strategy
      ready.input.word ready.middle.tau ready.middle.alpha0 ready.prepared.query
      ready.middle.rho ready.input.coins source.ordinary
      ready.prepared.relationIncrement).isSome = true := by
  rw [source.causalWord]
  exact produced_consumes (ringArithmetic (1 / 4 : K)).toArithmetic
    source.early source.strategy ready.middle.tau ready.middle.alpha0
    ready.prepared.query ready.middle.rho ready.input.coins source.ordinary
    ready.prepared.relationIncrement

structure TerminalCertificate {view : RawHashInput → Digest208}
    (ready : Ready view) (source : SourceRelationProducer ready)
    (c1 c2 : AnswerPrefix) (fullLog : OrderedRawQueryLog) : Prop where
  scalar : ScalarOutcome ready.prepared c1 c2 fullLog
  consumed : (consume (ringArithmetic (1 / 4 : K)).toArithmetic source.strategy
    ready.input.word ready.middle.tau ready.middle.alpha0 ready.prepared.query
    ready.middle.rho ready.input.coins source.ordinary
    ready.prepared.relationIncrement).isSome = true
  terminalAccepted : terminalCheck ready source = true

/-- The accepted branch supplies the literal final premise of
`produced_check_constructs_terminal_zero`, after transporting the canonical
word through the causal source equality. -/
theorem TerminalCertificate.accepted_on_produced
    {view : RawHashInput → Digest208} {ready : Ready view}
    {source : SourceRelationProducer ready} {c1 c2 : AnswerPrefix}
    {fullLog : OrderedRawQueryLog}
    (certificate : TerminalCertificate ready source c1 c2 fullLog) :
    check (1 / 4 : K)
      (produce source.early source.strategy ready.middle.tau ready.middle.alpha0
        ready.prepared.query ready.middle.rho ready.input.coins)
      source.terminalWeight (initialClaim ready source) ready.input.coins = true := by
  rw [← source.causalWord]
  exact certificate.terminalAccepted

inductive Outcome {view : RawHashInput → Digest208}
    (ready : Ready view) (source : SourceRelationProducer ready)
    (c1 c2 : AnswerPrefix) (fullLog : OrderedRawQueryLog) : Prop where
  | terminalRejected : terminalCheck ready source = false →
      Outcome ready source c1 c2 fullLog
  | terminalAccepted : TerminalCertificate ready source c1 c2 fullLog →
      Outcome ready source c1 c2 fullLog

/-- Execute the terminal comparison after constructing consumer success. -/
theorem run_terminal {view : RawHashInput → Digest208}
    (ready : Ready view) (source : SourceRelationProducer ready)
    (c1 c2 : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (scalar : ScalarOutcome ready.prepared c1 c2 fullLog) :
    Outcome ready source c1 c2 fullLog := by
  have consumed := consume_is_some ready source
  cases accepted : terminalCheck ready source with
  | false => exact Outcome.terminalRejected accepted
  | true => exact Outcome.terminalAccepted ⟨scalar, consumed, accepted⟩

#print axioms consume_is_some
#print axioms TerminalCertificate.accepted_on_produced
#print axioms run_terminal

end
end AspisV8Completion.SameBodyChronologicalRelationTerminal
