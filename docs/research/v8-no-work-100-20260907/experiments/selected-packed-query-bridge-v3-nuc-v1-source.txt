import PackedQueryRecord
import SelectedQueryBuffer

/-! Parsed 621-byte records to the same ordered query residual. The observed
word below is constructed AFTER the records; it is not a commitment binding
or a pre-query causal oracle. Existing source/inverse/fold theorems are reused
without eliminating equalities between concrete QM31 reciprocals. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedPackedQueryBridge
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7MerkleQueryGrammar
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
open AspisV8.PackedQueryRecord
open scoped BigOperators

section Generic
variable {J I S V : Type*}

/-- Fill only the observed fibres, with an arbitrary default elsewhere.
No fixing-time assertion is part of this deterministic extension. -/
def extendRows (queries : J → I) (values : J → S → V) (fallback : V)
    (point : I) (slot : S) : V := by
  classical
  exact if h : ∃ j, queries j=point then values (Classical.choose h) slot else fallback

theorem extendRows_at (queries : J → I) (distinct : Function.Injective queries)
    (values : J → S → V) (fallback : V) (j : J) (slot : S) :
    extendRows queries values fallback (queries j) slot=values j slot := by
  classical
  unfold extendRows
  split
  · rename_i h
    rw [distinct (Classical.choose_spec h)]
  · rename_i h
    exact False.elim (h ⟨j,rfl⟩)

/-- Pure symbolic fold congruence: no concrete inverse or field normal form
is inspected when this is instantiated on checked source arrays. -/
theorem expanded_congr {R : Type*} [CommRing R] (h a ix iy : R)
    (u v : Fin 4 → R) (same : u=v) :
    QuotientFold.expanded h a ix iy (u 0) (u 1) (u 2) (u 3)=
      QuotientFold.expanded h a ix iy (v 0) (v 1) (v 2) (v 3) := by
  rw [same]

end Generic

abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Gamma-combined raw records, extended at observed query indices only.
This word may depend on gamma, alpha, queries and all supplied records. -/
def observedWord {q : Nat} (gamma : K) (records : Fin q → List Byte)
    (queries : Fin q → Fin 262144) : Fin 1048576 → K := fun symbol =>
  extendRows queries (fun i => rawCombined gamma (records i)) 0
    (parentIndex symbol) (slotIndex (n:=262144) symbol)

theorem observedWord_at {q : Nat} (gamma : K) (records : Fin q → List Byte)
    (queries : Fin q → Fin 262144) (distinct : Function.Injective queries)
    (i : Fin q) (slot : Fin 4) :
    observedWord gamma records queries (childIndex (queries i) slot)=
      rawCombined gamma (records i) slot := by
  simp only [observedWord,parentIndex_childIndex,slotIndex_childIndex]
  exact extendRows_at queries distinct _ 0 i slot

/-- The source computes these four numerator-times-inverse values in record
ordinal order. C1 slot order and C2 helper/slot/tower order are inside combined. -/
def recordSlots {q : Nat} (d : Data (K:=K)) (decoded : Fin q → Decoded)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (i : Fin q) : Fin 4 → K := fun slot =>
  (combined d.gamma (decoded i) slot -
    (d.intercept+d.slope*selected d.useX
      (QueriedResidual.xs (exactCircleX (queries i)) slot)
      (QueriedResidual.ys (exactCircleY (queries i)) slot))) *
    QueriedResidual.inverseAt out i slot

/-- An external word can replace the constructed observation word only with
this explicit local equality. Parsing alone never supplies authentication. -/
theorem matching_slots {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (word : Fin 1048576 → K)
    (matchAt : ∀ i slot, word (childIndex (queries i) slot)=rawCombined d.gamma (records i) slot)
    (i : Fin q) :
    recordSlots d decoded queries out i=QueriedResidual.sourceSlots d word queries out i := by
  funext slot
  unfold recordSlots QueriedResidual.sourceSlots QueriedResidual.sourceNumerator
  rw [combined_eq_raw _ _ (parsed i),matchAt i slot]

-- Scalar inverse arrays are identical on both sides. Never normalize their
-- nested field implementations merely to transport the already equal slots.
attribute [local irreducible] recordSlots QueriedResidual.sourceSlots
attribute [local irreducible] combined rawCombined

def recordFold {q : Nat} (d : Data (K:=K)) (decoded : Fin q → Decoded)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (alpha : K) (i : Fin q) : K :=
  let v := recordSlots d decoded queries out i
  QuotientFold.expanded (1/2) alpha (QueriedResidual.baseInverseAt out i false)
    (QueriedResidual.baseInverseAt out i true) (v 0) (v 1) (v 2) (v 3)

theorem matching_fold {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (word : Fin 1048576 → K)
    (matchAt : ∀ i slot, word (childIndex (queries i) slot)=rawCombined d.gamma (records i) slot)
    (alpha : K) (i : Fin q) :
    recordFold d decoded queries out alpha i=QueriedResidual.sourceFold d word queries out alpha i := by
  unfold recordFold QueriedResidual.sourceFold
  exact expanded_congr (R:=K) (1/2) alpha
    (QueriedResidual.baseInverseAt out i false) (QueriedResidual.baseInverseAt out i true)
    (recordSlots d decoded queries out i) (QueriedResidual.sourceSlots d word queries out i)
    (matching_slots d records decoded parsed queries out word matchAt i)

attribute [local irreducible] recordFold QueriedResidual.sourceFold

/-- The mathematical chord quotient is DERIVED from parsed values and the
checked ordered inverse constructor. No supplied quotient equation. -/
theorem observed_quotient_slots {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (distinct : Function.Injective queries)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (i : Fin q) :
    recordSlots d decoded queries out i=fun slot =>
      SelectedQuotientOriginal.virtual d (observedWord d.gamma records queries)
        (childIndex (queries i) slot) := by
  exact (matching_slots d records decoded parsed queries out _
    (observedWord_at d.gamma records queries distinct) i).trans
    (QueriedResidual.success_slots d _ queries (QueriedResidual.baseList queries) out
      ((SelectedQueryBuffer.inverse_eq d queries).symm.trans inverse) i)

/-- These are the received values used by the typed terminal recurrence,
for the SAME observation-word quotient. Alpha may be zero and final adaptive. -/
theorem observed_fold {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (distinct : Function.Injective queries)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha : K) (i : Fin q) :
    recordFold d decoded queries out alpha i=
      ((SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
        (SelectedQuotientOriginal.virtual d (observedWord d.gamma records queries))).folded alpha)
        (storedPoint (K:=K) (queries i)) := by
  exact (matching_fold d records decoded parsed queries out _
    (observedWord_at d.gamma records queries distinct) alpha i).trans
    (QueriedResidual.success_fold d _ queries out
      ((SelectedQueryBuffer.inverse_eq d queries).symm.trans inverse) alpha i)

theorem observed_residual {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (distinct : Function.Injective queries)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha : K) (final : Fin 256 → K) (i : Fin q) :
    exactFinalLinear final (queries i)-recordFold d decoded queries out alpha i=
      PostQueryFunctional.residual final (fun j=>storedPoint (K:=K) (queries j))
        ((SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
          (SelectedQuotientOriginal.virtual d (observedWord d.gamma records queries))).folded alpha) i := by
  exact (congrArg (fun v : K=>exactFinalLinear final (queries i)-v)
    (matching_fold d records decoded parsed queries out _
      (observedWord_at d.gamma records queries distinct) alpha i)).trans
    (SelectedQueryBuffer.success_residual d _ queries out inverse alpha final i)

/-- Sorting authentication entries does not reorder this shifted-rho sum.
This is a family of q22 records, not a union or an independence assertion. -/
theorem q22_received_sum (d : Data (K:=K))
    (records : Fin 22 → List Byte) (decoded : Fin 22 → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin 22 → Fin 262144) (distinct : Function.Injective queries)
    (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha rho : K) :
    (∑ i : Fin 22, rho^(i.val+1)*recordFold d decoded queries out alpha i)=
      ∑ i : Fin 22, rho^(i.val+1)*
        ((SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
          (SelectedQuotientOriginal.virtual d (observedWord d.gamma records queries))).folded alpha)
          (storedPoint (K:=K) (queries i)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v : K=>rho^(i.val+1)*v)
    (observed_fold d records decoded parsed queries distinct out inverse alpha i)

/-- Explicit rejection, not reliance on totalized division at zero. -/
theorem source_pole_reject {q : Nat} (d : Data (K:=K))
    (queries : Fin q → Fin 262144) (i : Fin q) (slot : Fin 4)
    (pole : QueriedResidual.sourceDenom d (queries i) slot=0) :
    LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=none := by
  apply SelectedQueryBuffer.queried_pole_reject d queries i slot
  exact (QueriedResidual.sourceDenom_eq d (queries i) slot).symm.trans pole

#print axioms expanded_congr
#print axioms extendRows_at
#print axioms observedWord_at
#print axioms matching_slots
#print axioms matching_fold
#print axioms observed_quotient_slots
#print axioms observed_fold
#print axioms observed_residual
#print axioms q22_received_sum
#print axioms source_pole_reject
end
end AspisV8.SelectedPackedQueryBridge
