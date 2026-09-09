import CommonFibreGaoRecovery
import NearGammaSelectedC1

/-! A C1-only recovery consequence, independent of every later final or C2.
The received oracle and public sample, not the candidate coefficients, are
inputs to the decoder. The optional object's support is derived from its
definition. Fresh private sampling and authenticated/replay access are NOT
assumed to follow from a Merkle root or proof acceptance.

The exact-encoder/coordinate identity and public inverse matrix remain
explicit source-algebra interfaces. No payment-validity premise appears. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.EarlyC1GaoRecovery
open Finset Matrix
open AspisV8.EarlyC1Projection AspisV8.NearGammaFibreBridge
open AspisV8.GaoC1Recovery AspisV8.CommonFibreGaoRecovery
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
noncomputable local instance : Fintype (Fin 262144) :=
  AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p

def badFibres (received : C1Received) (p : C1Messages) : Finset (Fin 262144) :=
  univ \ support fibreEncode (receivedFibres received) p

/-- Returning some from the original optional object supplies its own
support; the support is not a new candidate-membership premise. -/
theorem badFibres_card (received : C1Received) (p : C1Messages)
    (found : earlyC1 received=some p) : (badFibres received p).card≤16535 := by
  have own := some_early_has_support fibreEncode (receivedFibres received) 245609 p found
  have count := card_sdiff_add_card_eq_card
    (subset_univ (support fibreEncode (receivedFibres received) p))
  change (badFibres received p).card+_= _ at count
  rw [AspisV8.NearGammaSelectedC1.domain_card] at count
  omega

def semanticLane (column : Fin 16) : Fin 26 := ⟨column.val, by omega⟩

/-- Four actual consecutive stored circle slots per selected distinct fibre. -/
def sampledIndex (sample : Fin 513 ↪ Fin 262144) (j : Fin (513*4)) : Fin 1048576 :=
  fibreEmbed (sample (finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2)

theorem sampledIndex_injective (sample : Fin 513 ↪ Fin 262144) :
    Function.Injective (sampledIndex sample) := by
  intro a b equality
  have pairEq := fibreEmbed.injective equality
  have firstEq := congrArg (fun pair : Fin 262144 × Fin 4 => pair.1) pairEq
  have secondEq := congrArg (fun pair : Fin 262144 × Fin 4 => pair.2) pairEq
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (sample.injective firstEq) secondEq

def sampledBad (received : C1Received) (p : C1Messages)
    (sample : Fin 513 ↪ Fin 262144) : Finset (Fin 513) :=
  univ.filter fun f => sample f ∈ badFibres received p

def sampleSet (sample : Fin 513 ↪ Fin 262144) : Finset (Fin 262144) := univ.map sample

theorem sampleSet_card (sample : Fin 513 ↪ Fin 262144) : (sampleSet sample).card=513 := by
  rw [sampleSet,card_map,Finset.card_univ,Fintype.card_fin]

/-- Ordered distinct sampling and the unordered private subset have exactly
the same bad-fibre count. No independent per-column sampling is introduced. -/
theorem sampledBad_card (received : C1Received) (p : C1Messages)
    (sample : Fin 513 ↪ Fin 262144) :
    (sampledBad received p sample).card=
      (sampleSet sample ∩ badFibres received p).card := by
  have sets : (sampledBad received p sample).map sample=
      sampleSet sample ∩ badFibres received p := by
    ext f
    constructor
    · intro hf
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hf
      exact mem_inter.mpr ⟨mem_map.mpr ⟨j,mem_univ _,rfl⟩,(mem_filter.mp hj).2⟩
    · intro hf
      obtain ⟨j,hj,rfl⟩ := mem_map.mp (mem_inter.mp hf).1
      exact mem_map.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,(mem_inter.mp hf).2⟩,rfl⟩
  exact (card_map sample).symm.trans (congrArg Finset.card sets)

def sampledWord (received : C1Received) (sample : Fin 513 ↪ Fin 262144)
    (column : Fin 16) : Fin (513*4) → K :=
  fun j => received (semanticLane column) (sampledIndex sample j)

/-- The executable-model decoder's inputs contain only sampled received
values and public algebraic parameters. p is deliberately absent. -/
def recoverSemantic (received : C1Received) (sample : Fin 513 ↪ Fin 262144)
    (bits : Bits) (i : K) (x y : Fin 1048576 → K)
    (tx ty : Row → K) (B : Matrix Row Row K) : Fin 16 → Option Message :=
  fun column => GaoC1Recovery.recover bits i
    (fun j => x (sampledIndex sample j)) (fun j => y (sampledIndex sample j))
    (sampledWord received sample column) tx ty B

theorem sampled_outside (received : C1Received) (p : C1Messages)
    (sample : Fin 513 ↪ Fin 262144) (bits : Bits) (x y : Fin 1048576 → K)
    (encoder : ∀ (message : Message) (index : Fin 1048576),
      value bits message (x index) (y index)=exactInitialEncoder message index)
    (column : Fin 16) (j : Fin (513*4))
    (outside : sampleFibre j ∉ sampledBad received p sample) :
    value bits (p (semanticLane column)) (x (sampledIndex sample j))
      (y (sampledIndex sample j))=sampledWord received sample column j := by
  letI : DecidablePred (fun a : Fin 262144 =>
    ∀ lane : Fin 26, receivedFibres received lane a=fibreEncode (p lane) a) :=
    fun _ => Classical.propDecidable _
  have notBad : sample (sampleFibre j) ∉ badFibres received p := by
    intro h
    exact outside (mem_filter.mpr ⟨mem_univ _,h⟩)
  have good : sample (sampleFibre j) ∈ support fibreEncode (receivedFibres received) p := by
    by_contra h
    exact notBad (mem_sdiff.mpr ⟨mem_univ _,h⟩)
  have agreement := congrFun ((mem_filter.mp good).2 (semanticLane column))
    (finProdFinEquiv.symm j).2
  rw [encoder]
  exact agreement.symm

/-- One common sample controls all sixteen columns. This consumes Gao
completeness on arbitrary received values; successful decoding is derived.
No final-distance, C2, semantic challenge or claimed witness is an input. -/
theorem failure_requires_129 (received : C1Received) (p : C1Messages)
    (sample : Fin 513 ↪ Fin 262144)
    (i h g : K) (hi : i^2= -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Bits) (x y : Fin 1048576 → K)
    (encoder : ∀ (message : Message) (index : Fin 1048576),
      value bits message (x index) (y index)=exactInitialEncoder message index)
    (circles : ∀ index, (x index)^2+(y index)^2=1)
    (distinct : Function.Injective (fun index => x index+i*y index))
    (tx ty : Row → K) (targetCircles : ∀ j, (tx j)^2+(ty j)^2=1)
    (B : Matrix Row Row K) (inverse : B*evaluationMatrix bits tx ty=1)
    (failure : recoverSemantic received sample bits i x y tx ty B ≠
      fun column => some (p (semanticLane column))) :
    129≤(sampledBad received p sample).card := by
  exact selected_failure_requires_129 i h g hi hh hg bits
    (fun column => p (semanticLane column))
    (fun j => x (sampledIndex sample j)) (fun j => y (sampledIndex sample j))
    (sampledWord received sample) (fun j => circles (sampledIndex sample j))
    (distinct.comp (sampledIndex_injective sample)) (sampledBad received p sample)
    (sampled_outside received p sample bits x y encoder) tx ty targetCircles B inverse failure

/-- A concrete total accounting endpoint for the mathematical early object:
its common bad set has size at most16535, and failure of this same oracle-
sampled decoder entails at least129 bad sample fibres. Authentication,
sampling law, implementation cost and payment constraints remain separate. -/
theorem early_failure_reduction (received : C1Received) (p : C1Messages)
    (found : earlyC1 received=some p) (sample : Fin 513 ↪ Fin 262144)
    (i h g : K) (hi : i^2= -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Bits) (x y : Fin 1048576 → K)
    (encoder : ∀ (message : Message) (index : Fin 1048576),
      value bits message (x index) (y index)=exactInitialEncoder message index)
    (circles : ∀ index, (x index)^2+(y index)^2=1)
    (distinct : Function.Injective (fun index => x index+i*y index))
    (tx ty : Row → K) (targetCircles : ∀ j, (tx j)^2+(ty j)^2=1)
    (B : Matrix Row Row K) (inverse : B*evaluationMatrix bits tx ty=1) :
    (badFibres received p).card≤16535 ∧
      ((recoverSemantic received sample bits i x y tx ty B ≠
        fun column => some (p (semanticLane column))) →
      129≤(sampleSet sample ∩ badFibres received p).card) := by
  refine ⟨badFibres_card received p found,?_⟩
  intro failure
  rw [← sampledBad_card]
  exact failure_requires_129 received p sample i h g hi hh hg bits x y encoder
    circles distinct tx ty targetCircles B inverse failure

#print axioms badFibres_card
#print axioms sampledIndex_injective
#print axioms sampleSet_card
#print axioms sampledBad_card
#print axioms sampled_outside
#print axioms failure_requires_129
#print axioms early_failure_reduction
end
end AspisV8.EarlyC1GaoRecovery
