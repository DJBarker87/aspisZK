import SameBodySourceRelationProducer
import SelectedCopyActiveFlat
import InterleavedChordRows
import ImageCallbackInterfaces

/-!
# Same-body dense reference terminal weight

This leaf removes the arbitrary 256-entry terminal weight from the functional
relation producer.  It constructs the original public covector from the
literal selected inactive-row table and the three repaired point rows,
applies the proved chord transpose, installs the carried image weights, and
performs the first arity-four dual fold at the actual `alpha0`.

This is the dense mathematical reference.  Equality of the selected
structured Rust contraction with this reference remains a separate machine
refinement; no performance claim follows from this construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.SameBodySourceTerminalWeight

open scoped BigOperators
open SameBodySourceRelationProducer SameBodyChronologicalRelationTerminal
open SameBodyLiveRelationObservation SameBodyAuthenticatedIncrement
open AspisV8Completion.SelectedCopyActiveFlat
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.InterleavedChordRows AspisV8.ImageCallbackInterfaces
open AspisV5FriRelationCandidateBridge
open AspisPool.V7MerkleQueryGrammar

abbrev K := SameBodySourceRelationProducer.K
abbrev Query := SameBodyChronologicalRelationTerminal.Query

noncomputable section

local instance : NeZero (2 : K) := AspisV8.SelectedReceivedOracle.twoNonzero

/-- The source's coefficient-side inactive bit, obtained from the same frozen
`ACTIVE_ROW_MASKS` table used by the selected Copy callback. -/
def inactiveCoefficient (index : Fin 1024) : K :=
  if rowActive index then 0 else 1

/-- Dense specification of `Description::entry`: one inactive-mask bit plus
the three repaired scalar-weighted multilinear point rows. -/
def originalWeight {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) : Fin 1024 → K := fun index =>
  inactiveCoefficient index + ∑ row : Fin 3,
    ordinary.value.prepared.scales row *
      mleRowWeight (SameBodyPublicCorrection.points ordinaryOps ordinary.z row) index

/-- The exact mathematical chord transpose used by the quotient relation. -/
def transformedWeight {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) : Fin 1024 → K :=
  transpose (ordinary.value.prepared.abc 0) (ordinary.value.prepared.abc 1)
    (ordinary.value.prepared.abc 2) (originalWeight ordinary)

/-- Post-image, post-alpha0 covector consumed before query injection.  The
three image coordinates and their signs are the proved selected convention. -/
def foldedWeight {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) : Fin 256 → K :=
  dualWeightFoldLayer 256 ready.middle.alpha0
    (imageWeights (transformedWeight ordinary)
      ⟨1023, by decide⟩ ⟨1022, by decide⟩ ⟨1021, by decide⟩
      ready.middle.tau (ordinary.value.prepared.abc 1)
      (ordinary.value.prepared.abc 2))

/-- Only the legal causal relation strategy remains.  Unlike the preceding
interface, no terminal covector can be supplied by the caller. -/
structure CausalStrategyRemainder {view : RawHashInput → Digest208}
    (ready : Ready view) where
  strategy : SameBodyRelation.Strategy K Query
  causalWord : ready.input.word = SameBodyRelation.produce
    (SameBodyAssembly.early ready.input.word) strategy ready.middle.tau
    ready.middle.alpha0 ready.prepared.query ready.middle.rho ready.input.coins

/-- Construct the older remainder interface with the derived dense terminal
weight. -/
def denseRemainder {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) (causal : CausalStrategyRemainder ready) :
    CausalRemainder ready where
  strategy := causal.strategy
  terminalWeight := foldedWeight ordinary
  causalWord := causal.causalWord

/-- Complete the functional source producer without an arbitrary ordinary
scalar or terminal covector. -/
def completeDense {view : RawHashInput → Digest208} {ready : Ready view}
    (ordinary : OrdinaryReady ready) (causal : CausalStrategyRemainder ready) :
    SourceRelationProducer ready :=
  complete ordinary (denseRemainder ordinary causal)

theorem completeDense_ordinary {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready)
    (causal : CausalStrategyRemainder ready) :
    (completeDense ordinary causal).ordinary = ordinary.value.claim := by
  rfl

theorem completeDense_terminalWeight {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready)
    (causal : CausalStrategyRemainder ready) :
    (completeDense ordinary causal).terminalWeight = foldedWeight ordinary := by
  rfl

theorem completeDense_causalWord {view : RawHashInput → Digest208}
    {ready : Ready view} (ordinary : OrdinaryReady ready)
    (causal : CausalStrategyRemainder ready) :
    ready.input.word = SameBodyRelation.produce
      (completeDense ordinary causal).early
      (completeDense ordinary causal).strategy ready.middle.tau
      ready.middle.alpha0 ready.prepared.query ready.middle.rho ready.input.coins := by
  exact causal.causalWord

#print axioms completeDense_ordinary
#print axioms completeDense_terminalWeight
#print axioms completeDense_causalWord

end
end AspisV8Completion.SameBodySourceTerminalWeight
