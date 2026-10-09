import SelectedPackedQueryBridgeV3
import TypedRelationTerminalV3

/-! Conditional deterministic composition. A fixed total word is an explicit
input, and equality with each parsed opening is a hypothesis, not inferred
from parsing or a post-query extension. No commitment or freshness theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 400
set_option maxHeartbeats 200000

namespace AspisV8.FixedWordQueryTerminal
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriRelationCandidateBridge
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7MerkleQueryGrammar
open AspisV8.OptimizedRelationRefinement AspisV8.PostQueryFunctional
open AspisV8.FirstImageDiscrepancy AspisV8.CausalOrderedRelation
open AspisV8.TypedRelationTerminal AspisV8.PackedQueryRecord
open scoped BigOperators

section Generic
variable {F : Type*} [Field F] [DecidableEq F]

/-- The literal typed recurrence takes a list of opened values in ordinal
order, rather than a total field-indexed function. This is the SAME plus
query injection and deferred image term as TypedRelationTerminalV3. -/
def acceptsValues {q : Nat} (p : Prefix (K:=F)) (final : Fin 256 → F)
    (points opening : Fin q → F) (rho : F) (t : TailFields (K:=F))
    (a1 a2 a3 : F) : Prop :=
  let f := tailPrimal final a1 a2 a3
  let start := sourceHorner p.quarter p.claim p.response0 p.alpha0+
    ∑ j, rho^(j.val+1)*opening j
  candidateClaim (fun i=>ordinaryTerminal p a1 a2 a3 i+
    tailDual (queryWeights points rho) a1 a2 a3 i) f+
    imageTerminal p.tau p.b p.c p.alpha0 a1 a2 a3*f 3 =
      sourceHorner p.quarter
        (sourceHorner p.quarter (sourceHorner p.quarter start t.first a1)
          (t.second a1) a2) (t.third a1 a2) a3

theorem values_source_iff {q : Nat} (p : Prefix (K:=F)) (final : Fin 256 → F)
    (points opening : Fin q → F) (received : F → F) (rho : F)
    (t : TailFields (K:=F)) (a1 a2 a3 : F)
    (same : ∀ j, opening j=received (points j)) :
    acceptsValues p final points opening rho t a1 a2 a3 ↔
      sourceAccepts p final points received rho t a1 a2 a3 := by
  have sumSame : (∑ j, rho^(j.val+1)*opening j)=
      ∑ j, rho^(j.val+1)*received (points j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [same j]
  unfold acceptsValues sourceAccepts terminalClaim
  rw [first_claim_horner,sumSame]

end Generic

abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Supplied before tau/alpha/query continuation. The caller still has to
construct this SAME object from the real earlier transcript across histories.
The chord coefficients used in quotient and image checks cannot diverge. -/
structure FixedInput where
  chord : OODInterpolant.Data (K:=K)
  word : Fin 1048576 → K
  ordinary : Fin 1024 → K
  referenceQ : Fin 1024 → K
  claim : K
  quarter : K

def FixedInput.before (fixed : FixedInput) : Before (K:=K) where
  ordinary := fixed.ordinary
  referenceQ := fixed.referenceQ
  claim := fixed.claim
  quarter := fixed.quarter
  b := fixed.chord.b
  c := fixed.chord.c

def FixedInput.oracle (fixed : FixedInput) :
    FixedOracle SelectedReceivedOracle.domain SelectedReceivedOracle.domain fixed.before.referenceQ :=
  SelectedReceivedOracle.oracle fixed.referenceQ (SelectedQuotientOriginal.virtual fixed.chord fixed.word)

def indices {q : Nat} (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q) :
    Fin q → Fin 262144 := fun i=>SelectedReceivedOracle.index (queries i)

theorem indexed_point {q : Nat}
    (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q) (i : Fin q) :
    storedPoint (K:=K) (indices queries i)=(queries i : K) :=
  SelectedReceivedOracle.point_index (queries i) (queries i).property

/-- This is the missing authenticated opening interface, exposed explicitly.
It fixes the total word, while records may be adaptive query responses. -/
def OpeningEquality {q : Nat} (fixed : FixedInput)
    (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q)
    (records : Fin q → List Byte) : Prop :=
  ∀ i slot, fixed.word (childIndex (indices queries i) slot)=
    rawCombined fixed.chord.gamma (records i) slot

def openedValues {q : Nat} (fixed : FixedInput) (decoded : Fin q → Decoded)
    (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q)
    (out : List K × List M31Exact) (alpha : K) : Fin q → K :=
  SelectedPackedQueryBridge.recordFold fixed.chord decoded (indices queries) out alpha

/-- No observedWord is used: transport is to the explicitly fixed total word.
Only the prior checked matching_slots/matching_fold interfaces are consumed. -/
theorem received_fixed {q : Nat} (fixed : FixedInput)
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q)
    (opening : OpeningEquality fixed queries records)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines fixed.chord.a fixed.chord.b fixed.chord.c
      (SelectedQueryBuffer.points (indices queries))=some out)
    (alpha : K) (i : Fin q) :
    openedValues fixed decoded queries out alpha i=fixed.oracle.folded alpha (queries i) := by
  have checked := (SelectedQueryBuffer.inverse_eq fixed.chord (indices queries)).symm.trans inverse
  have first := (SelectedPackedQueryBridge.matching_fold fixed.chord records decoded parsed
    (indices queries) out fixed.word opening alpha i).trans
    (QueriedResidual.success_fold fixed.chord fixed.word (indices queries) out checked alpha i)
  have reference :=
    (SelectedReceivedOracle.oracle_folded (0 : Fin 1024 → K)
      (SelectedQuotientOriginal.virtual fixed.chord fixed.word) alpha (indices queries i)).trans
    (SelectedReceivedOracle.oracle_folded fixed.referenceQ
      (SelectedQuotientOriginal.virtual fixed.chord fixed.word) alpha (indices queries i)).symm
  exact (first.trans reference).trans
    (congrArg (fun point : K=>fixed.oracle.folded alpha point) (indexed_point queries i))

theorem residual_fixed {q : Nat} (fixed : FixedInput)
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain q)
    (opening : OpeningEquality fixed queries records)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines fixed.chord.a fixed.chord.b fixed.chord.c
      (SelectedQueryBuffer.points (indices queries))=some out)
    (alpha : K) (final : Fin 256 → K) (i : Fin q) :
    exactFinalLinear final (indices queries i)-openedValues fixed decoded queries out alpha i=
      PostQueryFunctional.residual final (fun j=>(queries j : K)) (fixed.oracle.folded alpha) i := by
  have evaluation := (SelectedReceivedOracle.final_evaluation final (indices queries i)).symm.trans
    (congrArg (lineEval final) (indexed_point queries i))
  exact congrArg₂ (fun left right => left - right) evaluation
    (received_fixed fixed records decoded parsed queries opening out inverse alpha i)

/-- q22 source terminal acceptance iff the causal game's terminal acceptance,
under the explicit fixed-word opening premise and checked parser/inverse path.
The SAME response0, final256, later responses and ordinal schedule occur on
both sides. No earlier semantic acceptance or fresh challenge law is inferred. -/
theorem acceptance_fixed (fixed : FixedInput)
    (fields : TypedRelationTerminal.Fields SelectedReceivedOracle.domain 22)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain 22)
    (rho a1 a2 a3 : K) (records : Fin 22 → List Byte) (decoded : Fin 22 → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (opening : OpeningEquality fixed queries records)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines fixed.chord.a fixed.chord.b fixed.chord.c
      (SelectedQueryBuffer.points (indices queries))=some out) :
    acceptsValues (fixed.before.snapshot tau (fields.firstResponse tau) alpha)
      (fields.final tau alpha) (fun j=>(queries j : K)) (openedValues fixed decoded queries out alpha)
      rho (fields.later tau alpha queries rho) a1 a2 a3 ↔
    CausalOrderedRelation.accepts fixed.before fixed.oracle fields.strategy
      tau alpha queries rho [a1,a2,a3] := by
  exact (values_source_iff _ _ _ _ _ rho _ a1 a2 a3
    (received_fixed fixed records decoded parsed queries opening out inverse alpha)).trans
    (TypedRelationTerminal.source_accepts_iff fixed.before fixed.oracle fields
      tau alpha queries rho a1 a2 a3)

/-- An externally proved authentication/collision dichotomy may be consumed;
this theorem neither constructs a collision nor bounds its probability. -/
theorem collision_or_acceptance (fixed : FixedInput)
    (fields : TypedRelationTerminal.Fields SelectedReceivedOracle.domain 22)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule SelectedReceivedOracle.domain 22)
    (rho a1 a2 a3 : K) (records : Fin 22 → List Byte) (decoded : Fin 22 → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i)) (collision : Prop)
    (binding : collision ∨ OpeningEquality fixed queries records)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines fixed.chord.a fixed.chord.b fixed.chord.c
      (SelectedQueryBuffer.points (indices queries))=some out)
    (accepted : acceptsValues (fixed.before.snapshot tau (fields.firstResponse tau) alpha)
      (fields.final tau alpha) (fun j=>(queries j : K)) (openedValues fixed decoded queries out alpha)
      rho (fields.later tau alpha queries rho) a1 a2 a3) :
    collision ∨ CausalOrderedRelation.accepts fixed.before fixed.oracle fields.strategy
      tau alpha queries rho [a1,a2,a3] := by
  rcases binding with bad | good
  · exact Or.inl bad
  · exact Or.inr ((acceptance_fixed fixed fields tau alpha queries rho a1 a2 a3
      records decoded parsed good out inverse).mp accepted)

#print axioms values_source_iff
#print axioms indexed_point
#print axioms received_fixed
#print axioms residual_fixed
#print axioms acceptance_fixed
#print axioms collision_or_acceptance
end
end AspisV8.FixedWordQueryTerminal
