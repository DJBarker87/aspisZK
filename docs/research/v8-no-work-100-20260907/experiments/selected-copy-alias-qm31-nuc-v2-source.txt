import SelectedCopyAliases
import AspisFormal.V5ComponentCQM31TowerExact

/-! Exact selected-field guards and the seven singleton amount links.
No field enumeration, old-registry cardinality, canonical decoder success,
or honestly generated trace is used. The selected source partition remains
explicitly collision-bearing; this does not assert every sampled proof
enforces alias equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedCopyAliasQM31
open scoped BigOperators
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedCopyAliases
noncomputable section

theorem selectedTag_small (index : Fin 136) : selectedTag index<P := by
  unfold selectedTag P
  omega

theorem qm31_tag_injective :
    Function.Injective (fun index : Fin 136 => (selectedTag index:QM31Exact)) := by
  intro left right equal
  apply selectedTag_injective
  have baseEqual : (selectedTag left:M31Exact)=(selectedTag right:M31Exact) := by
    apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
    calc
      algebraMap M31Exact QM31Exact (selectedTag left:M31Exact)=
          (selectedTag left:QM31Exact) := map_natCast _ _
      _ = (selectedTag right:QM31Exact) := equal
      _ = algebraMap M31Exact QM31Exact (selectedTag right:M31Exact) :=
        (map_natCast _ _).symm
  exact CharP.natCast_injOn_Iio M31Exact P
    (selectedTag_small left) (selectedTag_small right) baseEqual

theorem qm31_small_casts (n : Nat) (positive : 0<n) (bounded : n≤136) :
    (n:QM31Exact)≠0 := by
  have small : n<P := bounded.trans_lt (by decide : 136<P)
  have baseNonzero : (n:M31Exact)≠0 := by
    intro zero
    exact (Nat.not_dvd_of_pos_of_lt positive small)
      ((CharP.cast_eq_zero_iff M31Exact P n).mp zero)
  intro zero
  apply baseNonzero
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  calc
    algebraMap M31Exact QM31Exact (n:M31Exact)=(n:QM31Exact) := map_natCast _ _
    _ = 0 := zero
    _ = algebraMap M31Exact QM31Exact (0:M31Exact) := (map_zero _).symm

theorem active_count_le (variant : Variant) (appendIndex : Nat) :
    (activeLinks variant appendIndex).card≤136 := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem qm31_source_roots_or_aliases (table : Table QM31Exact)
    (variant : Variant) (appendIndex : Nat) (lambda chi : QM31Exact)
    (helper : Fin 1024 → QM31Exact)
    (localZero : ∀ row,selectedBooleanResidual
      (sourceRows table lambda variant appendIndex) helper chi row=0)
    (totalZero : (∑ row,helper row)=0)
    (inactiveZero : (∑ row,inactiveHelper rowActive helper row)=0)
    (noPole : ∀ row,rowActive row →
      NoSlotPole (sourceRows table lambda variant appendIndex row) chi) :
    WeightedAliases table variant appendIndex ∨
      (lambdaWitness table variant appendIndex≠0 ∧
        (lambdaWitness table variant appendIndex).eval lambda=0 ∧
        (lambdaWitness table variant appendIndex).natDegree≤
          16*(activeLinks variant appendIndex).card) ∨
      (chiWitness table variant appendIndex lambda≠0 ∧
        (chiWitness table variant appendIndex lambda).eval chi=0 ∧
        (chiWitness table variant appendIndex lambda).natDegree<
          2*(activeLinks variant appendIndex).card) := by
  exact source_roots_or_aliases table variant appendIndex lambda chi helper
    qm31_tag_injective
    (fun n positive bounded => qm31_small_casts n positive
      (bounded.trans (active_count_le variant appendIndex)))
    localZero totalZero inactiveZero noPole

def amountProducer : Fin 7 → Fin 1024 × Nat :=
  ![(44,0),(460,0),(508,0),(1008,10),(1010,10),(1012,10),(1014,2)]
def amountConsumer : Fin 7 → Fin 1024 × Nat :=
  ![(1008,10),(1010,10),(1012,10),(1014,0),(1014,1),(1015,1),(1015,0)]

def amountIndex (edge : Fin 7) : Fin 136 := ⟨11+edge.val,by omega⟩

def transferKind : WeightKind → Bool
  | .one | .transfer => true
  | _ => false

/-- Seven finite public metadata checks. No field/table expression is
normalized when checking the generated endpoint and singleton-pattern data. -/
theorem amount_source_shape : ∀ edge : Fin 7,
    transferKind (selectedKind (amountIndex edge))=true ∧
      (producer (amountIndex edge)).row=(amountProducer edge).1 ∧
      (consumer (amountIndex edge)).row=(amountConsumer edge).1 ∧
      sourcePatterns (producer (amountIndex edge)).pattern=
        ⟨1,(amountProducer edge).2,0⟩ ∧
      sourcePatterns (consumer (amountIndex edge)).pattern=
        ⟨1,(amountConsumer edge).2,0⟩ := by
  decide

theorem transfer_kind_weight {K : Type*} [Field K] (kind : WeightKind)
    (appendIndex : Nat) (good : transferKind kind=true) :
    publicWeight (K:=K) .transfer appendIndex kind=1 := by
  cases kind <;> simp_all [transferKind,publicWeight,weightBit]

/-- Source indices11..17, with transfer weights exactly one. The lookup
is computed from the actual sourceLinks and four singleton patterns. -/
theorem amount_link_lookup {K : Type*} [Field K] (table : Table K)
    (appendIndex : Nat) (edge : Fin 7) :
    selectedWeight (K:=K) .transfer appendIndex (amountIndex edge)=1 ∧
      patternLimb table (producer (amountIndex edge)) 0=
        table (amountProducer edge).1 (amountProducer edge).2 ∧
      patternLimb table (consumer (amountIndex edge)) 0=
        table (amountConsumer edge).1 (amountConsumer edge).2 := by
  obtain ⟨kind,producerRow,consumerRow,producerPattern,consumerPattern⟩ :=
    amount_source_shape edge
  refine ⟨transfer_kind_weight _ appendIndex kind,?_,?_⟩
  · simp [patternLimb,producerPattern,producerRow]
  · simp [patternLimb,consumerPattern,consumerRow]

/-- Actual weighted tuple aliases imply the seven raw field-cell aliases
consumed by SelectedAmountEndpoint, not equality to a supplied honest table. -/
theorem transfer_amount_aliases {K : Type*} [Field K] (table : Table K)
    (appendIndex : Nat) (aliases : WeightedAliases table .transfer appendIndex) :
    ∀ edge : Fin 7,table (amountProducer edge).1 (amountProducer edge).2=
      table (amountConsumer edge).1 (amountConsumer edge).2 := by
  intro edge
  have edgeResidual := aliases (amountIndex edge) 0
  obtain ⟨weight,producerEq,consumerEq⟩ := amount_link_lookup table appendIndex edge
  rw [weight,one_mul,producerEq,consumerEq] at edgeResidual
  exact sub_eq_zero.mp edgeResidual

#print axioms selectedTag_small
#print axioms qm31_tag_injective
#print axioms qm31_small_casts
#print axioms active_count_le
#print axioms qm31_source_roots_or_aliases
#print axioms amount_source_shape
#print axioms transfer_kind_weight
#print axioms amount_link_lookup
#print axioms transfer_amount_aliases
end
end AspisV8.SelectedCopyAliasQM31
