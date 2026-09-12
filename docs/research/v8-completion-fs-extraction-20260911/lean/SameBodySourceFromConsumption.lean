import SameBodySourceTerminalWeight
import SameBodyConsumeConstructsWord

/-!
# Source relation producer from checked causal consumption

This leaf removes the independently supplied whole-word equality from the
dense source producer.  The remaining strategy is a legal pre-tau staged
strategy, and its correspondence with the submitted word is constructed by
an actual successful `SameBodyRelation.consume` run.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000
set_option maxRecDepth 2000

namespace AspisV8Completion.SameBodySourceFromConsumption

open SameBodyRelation SameBodyConsumeConstructsWord
open SameBodySourceRelationProducer SameBodySourceTerminalWeight
open SameBodyChronologicalRelationTerminal SameBodyLiveRelationObservation
open SameBodyAuthenticatedIncrement
open SameBodyTerminalExecution
open SameBodyQueryClaimExact
open AspisV8.OptimizedRelationRefinement
open AspisPool.V7MerkleQueryGrammar

abbrev K := SameBodySourceRelationProducer.K
abbrev Query := SameBodyChronologicalRelationTerminal.Query

noncomputable section

/-- The source-side fact still required from chronological execution: one
legal staged strategy actually passed the same-word message consumer. -/
structure ConsumedStrategy {view : RawHashInput → Digest208}
    (ready : Ready view) (ordinary : OrdinaryReady ready) where
  strategy : Strategy K Query
  result : Result K
  consumed : consume (ringArithmetic (1 / 4 : K)).toArithmetic strategy
    ready.input.word ready.middle.tau ready.middle.alpha0 ready.prepared.query
    ready.middle.rho ready.input.coins ordinary.value.claim
    ready.prepared.relationIncrement = some result

/-- Consumer success constructs the exact same-word invariant needed by the
dense source producer. -/
def causalRemainder {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) (consumed : ConsumedStrategy ready ordinary) :
    CausalStrategyRemainder ready where
  strategy := consumed.strategy
  causalWord := consume_success_constructs_word
    (ringArithmetic (1 / 4 : K)).toArithmetic consumed.strategy
    ready.input.word ready.middle.tau ready.middle.alpha0 ready.prepared.query
    ready.middle.rho ready.input.coins ordinary.value.claim
    ready.prepared.relationIncrement consumed.result consumed.consumed

/-- Complete source producer with ordinary claim, terminal covector and
same-word causality all constructed. -/
def completeFromConsumption {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready)
    (consumed : ConsumedStrategy ready ordinary) : SourceRelationProducer ready :=
  completeDense ordinary (causalRemainder ordinary consumed)

theorem completeFromConsumption_causalWord
    {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) (consumed : ConsumedStrategy ready ordinary) :
    ready.input.word = produce
      (SameBodyAssembly.early ready.input.word) consumed.strategy
      ready.middle.tau ready.middle.alpha0 ready.prepared.query ready.middle.rho
      ready.input.coins := by
  exact (causalRemainder ordinary consumed).causalWord

#print axioms completeFromConsumption_causalWord

end
end AspisV8Completion.SameBodySourceFromConsumption
