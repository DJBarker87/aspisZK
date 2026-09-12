import SameBodyChronologicalRelationTerminal
import SameBodyOODData
import SameBodyPublicCorrection
import SameBodyAssembly

/-!
# Source construction of the ordinary relation scalar

This leaf removes the freely supplied ordinary scalar from
`SourceRelationProducer`.  It executes the selected repaired row batching,
OOD interpolation and public affine correction on the canonical same-body
word.  Inverse/preparation failure remains explicit.

The causal strategy equality and terminal weight remain the precise source
producer remainder.  The OOD-data provenance equality is also retained until
the chronological OOD constructor is spliced into the parent run.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SameBodySourceRelationProducer

open SameBodyChronologicalRelationTerminal SameBodyLiveRelationObservation
open SameBodyAuthenticatedIncrement SameBodyLiveTerminalInput
open SameBodyRelation SameBodyAssembly
open SameBodyOODData SameBodyOrdinary SameBodyPublicCorrection
open AspisV8.OODInterpolant
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7MerkleQueryGrammar

abbrev K := SameBodyAuthenticatedIncrement.K
abbrev Query := SameBodyChronologicalRelationTerminal.Query

noncomputable section

def ordinaryOps : SameBodyOrdinary.Arithmetic K where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  square := fun value => value * value
  tryInv := qm31TryInv

def firstPoint (data : Data (K := K)) : SameBodyOrdinary.Point K :=
  ⟨data.x0, data.y0⟩

def secondPoint (data : Data (K := K)) : SameBodyOrdinary.Point K :=
  ⟨data.x1, data.y1⟩

def corrected {view : RawHashInput → Digest208} (ready : Ready view)
    (z : Fin 10 → K) : Option (Corrected K) :=
  SameBodyPublicCorrection.correct ordinaryOps ready.input.word ready.gamma
    ready.middle.kappa (firstPoint ready.data) (secondPoint ready.data) z

structure OrdinaryReady {view : RawHashInput → Digest208}
    (ready : Ready view) where
  z : Fin 10 → K
  sourceData : fromSampled ready.out ready.gamma ready.body = some ready.data
  value : Corrected K
  valueRun : corrected ready z = some value

inductive OrdinaryOutcome {view : RawHashInput → Digest208}
    (ready : Ready view) (z : Fin 10 → K)
    (sourceData : fromSampled ready.out ready.gamma ready.body = some ready.data) :
    Type where
  | rejected : corrected ready z = none → OrdinaryOutcome ready z sourceData
  | produced : OrdinaryReady ready → OrdinaryOutcome ready z sourceData

/-- The executable ordinary constructor is total: inverse/domain failure is
not replaced by a default scalar. -/
def buildOrdinary {view : RawHashInput → Digest208} (ready : Ready view)
    (z : Fin 10 → K)
    (sourceData : fromSampled ready.out ready.gamma ready.body = some ready.data) :
    OrdinaryOutcome ready z sourceData :=
  match runEq : corrected ready z with
  | none => .rejected runEq
  | some value => .produced ⟨z, sourceData, value, runEq⟩

/-- The produced scalar is exactly the repaired row/OOD/public correction,
not an independent `ordinary : K` input. -/
theorem ordinary_claim_constructed {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready) :
    SameBodyOrdinary.prepare ordinaryOps ready.input.word ready.gamma
        ready.middle.kappa (firstPoint ready.data) (secondPoint ready.data) =
          some ordinary.value.prepared ∧
      ordinary.value.publicPair = pair ordinaryOps ordinary.z
        ready.middle.kappa ordinary.value.prepared.useX ∧
      ordinary.value.claim = ordinaryOps.sub
        (ordinaryOps.sub ordinary.value.prepared.uncorrectedClaim
          (ordinaryOps.mul ordinary.value.prepared.intercept
            ordinary.value.publicPair.1))
        (ordinaryOps.mul ordinary.value.prepared.slope
          ordinary.value.publicPair.2) := by
  exact correction_constructed ordinaryOps ready.input.word ready.gamma
    ready.middle.kappa (firstPoint ready.data) (secondPoint ready.data)
    ordinary.z ordinary.value ordinary.valueRun

/-- Everything still needed from the source after ordinary construction.
`early` is no longer supplied: it is the canonical word's literal prefix. -/
structure CausalRemainder {view : RawHashInput → Digest208}
    (ready : Ready view) where
  strategy : Strategy K Query
  terminalWeight : Fin 256 → K
  causalWord : ready.input.word = produce (early ready.input.word) strategy
    ready.middle.tau ready.middle.alpha0 ready.prepared.query ready.middle.rho
    ready.input.coins

/-- Complete the prior interface without reintroducing an arbitrary ordinary
scalar. -/
def complete {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) (remainder : CausalRemainder ready) :
    SourceRelationProducer ready where
  early := early ready.input.word
  strategy := remainder.strategy
  ordinary := ordinary.value.claim
  terminalWeight := remainder.terminalWeight
  causalWord := remainder.causalWord

theorem complete_ordinary {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready)
    (remainder : CausalRemainder ready) :
    (complete ordinary remainder).ordinary = ordinary.value.claim := by
  rfl

theorem complete_source_data {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready) :
    fromSampled ready.out ready.gamma ready.body = some ready.data :=
  ordinary.sourceData

#print axioms ordinary_claim_constructed
#print axioms complete_ordinary
#print axioms complete_source_data

end
end AspisV8Completion.SameBodySourceRelationProducer
