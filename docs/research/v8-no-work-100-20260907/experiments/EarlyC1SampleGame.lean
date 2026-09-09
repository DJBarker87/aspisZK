import EarlyC1GaoRecovery
import PrivateSampleMoment
import Mathlib.Data.Finset.Sort

/-! Accepted C1 coefficient-recovery failure, without any final-distance
premise. The private extractor takes only the received word, a uniform
513-subset and public algebraic data. The early candidate is a proof object,
not an input to recovery. Actual root/replay access and the explicitly named
encoder/inverse interfaces remain unproved here. This is NOT payment-witness
extraction: correct recovered coefficients may still fail payment validation. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.EarlyC1SampleGame
open Finset Matrix
open AspisV8.EarlyC1Projection AspisV8.EarlyC1GaoRecovery
open AspisV8.GaoC1Recovery AspisV8.PrivateSampleMoment
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p

structure PublicData where
  bits : Bits
  i : K
  h : K
  g : K
  x : Fin 1048576 → K
  y : Fin 1048576 → K
  tx : Row → K
  ty : Row → K
  matrix : Matrix Row Row K

/-- These are the remaining concrete code/matrix interfaces, not an assumed
decoder-success or valid-payment predicate. They are public and sample-independent. -/
structure AlgebraInterfaces (d : PublicData) : Prop where
  i_sq : d.i^2= -1
  half : 2*d.h=1
  ih : 2*d.i*d.g=1
  encoder : ∀ (message : Message) (index : Fin 1048576),
    value d.bits message (d.x index) (d.y index)=exactInitialEncoder message index
  circles : ∀ index, (d.x index)^2+(d.y index)^2=1
  distinct : Function.Injective (fun index => d.x index+d.i*d.y index)
  targets : ∀ j, (d.tx j)^2+(d.ty j)^2=1
  inverse : d.matrix*evaluationMatrix d.bits d.tx d.ty=1

def ordered (S : Finset (Fin 262144)) (h : S.card=513) : Fin 513 ↪ Fin 262144 :=
  (S.orderEmbOfFin h).toEmbedding

theorem ordered_set (S : Finset (Fin 262144)) (h : S.card=513) :
    sampleSet (ordered S h)=S := by
  exact S.map_orderEmbOfFin_univ h

def decode (d : PublicData) (received : C1Received) (S : Finset (Fin 262144)) :
    Fin 16 → Option Message :=
  if h : S.card=513 then
    recoverSemantic received (ordered S h) d.bits d.i d.x d.y d.tx d.ty d.matrix
  else fun _ => none

theorem decode_on_sample (d : PublicData) (received : C1Received)
    (S : Finset (Fin 262144)) (h : S.card=513) :
    decode d received S=
      recoverSemantic received (ordered S h) d.bits d.i d.x d.y d.tx d.ty d.matrix := by
  rw [decode,dif_pos h]

theorem failed_sample_has_129 (d : PublicData) (interfaces : AlgebraInterfaces d)
    (received : C1Received) (p : C1Messages) (S : Finset (Fin 262144))
    (h : S.card=513)
    (failure : decode d received S≠fun col => some (p (semanticLane col))) :
    129≤(S ∩ badFibres received p).card := by
  rw [decode_on_sample d received S h] at failure
  have hc := failure_requires_129 received p (ordered S h) d.i d.h d.g
    interfaces.i_sq interfaces.half interfaces.ih d.bits d.x d.y
    interfaces.encoder interfaces.circles interfaces.distinct d.tx d.ty
    interfaces.targets d.matrix interfaces.inverse failure
  rw [sampledBad_card,ordered_set] at hc
  exact hc

/-- The actual decoder supplies the bad-sample implication; it is not a
correspondence premise of this probability endpoint. `accept` may restrict
to any causal proof execution, including a far final, or depend on the
private sample. We bound the joint mass rather than claiming conditional
uniformity after acceptance. Received data and the early object precede the
fresh uniform private subset. -/
theorem accepted_coefficient_failure_bound (d : PublicData)
    (interfaces : AlgebraInterfaces d) (received : C1Received) (p : C1Messages)
    (found : earlyC1 received=some p) (accept : Finset (Fin 262144) → Prop) :
    ((((univ : Finset (Fin 262144)).powersetCard 513).filter fun S =>
      accept S ∧ decode d received S≠fun col => some (p (semanticLane col))).card : ℚ) /
      (univ : Finset (Fin 262144)).card.choose 513 ≤
        ceiling 262144 16535 513 129 104 := by
  apply selected_accepted_failure univ (badFibres received p)
    AspisV8.NearGammaSelectedC1.domain_card (subset_univ _)
    (badFibres_card received p found) accept
    (fun S => decode d received S≠fun col => some (p (semanticLane col)))
  intro S hS failure
  exact failed_sample_has_129 d interfaces received p S (mem_powersetCard.mp hS).2 failure

#print axioms ordered_set
#print axioms decode_on_sample
#print axioms failed_sample_has_129
#print axioms accepted_coefficient_failure_bound
end
end AspisV8.EarlyC1SampleGame
