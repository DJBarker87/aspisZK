import NearGammaSelectedC1
import ClaimTransport
import Mathlib.Algebra.BigOperators.Fin
import FiniteSumConcat

/-! Fixing the complete C1 as an original codeword removes its known
contribution from the received batch. The unknown received curve then has
three lanes and degree two. This does NOT give a degree-two bound on false
C1 claims: their scaled error is an explicit Laurent term retained below.
No helper membership, successful decoder or agreement premise is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 150000
namespace AspisV8.FixedC1HelperReduction
open Finset Polynomial
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.NearGammaSelectedC1 AspisV8.NearGammaFibreBridge
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p

def initialLinear : Message →ₗ[K] (Fin 1048576 → K) where
  toFun := exactInitialEncoder
  map_add' := AspisK1.V7ExactCorrelatedAgreement.exactInitialEncoder_add
  map_smul' := AspisK1.V7ExactCorrelatedAgreement.exactInitialEncoder_smul

theorem initialLinear_apply (message : Message) :
    initialLinear message=exactInitialEncoder message := rfl

def exactC1 (p : C1Messages) : C1Received := fun lane => exactInitialEncoder (p lane)
def c1Batch (p : C1Messages) (gamma : K) : Message :=
  ∑ lane : Fin 26, gamma^lane.val • p lane
def helperCurve (c2 : C2Received) (gamma : K) : Fin 1048576 → K :=
  fun index => ∑ lane : Fin 3, gamma^lane.val*c2 lane index
def lowClaims (claims : Fin 29 → K) (gamma : K) : K :=
  ∑ lane : Fin 26, gamma^lane.val*claims (Fin.castAdd 3 lane)
def helperClaims (claims : Fin 29 → K) (gamma : K) : K :=
  ∑ lane : Fin 3, gamma^lane.val*claims (Fin.natAdd 26 lane)

def helperPolynomial (c2 : C2Received) (index : Fin 1048576) : K[X] :=
  ∑ lane : Fin 3, monomial lane.val (c2 lane index)

theorem helperPolynomial_degree (c2 : C2Received) (index : Fin 1048576) :
    (helperPolynomial c2 index).natDegree≤2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro lane _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem helperPolynomial_eval (c2 : C2Received) (gamma : K) (index : Fin 1048576) :
    (helperPolynomial c2 index).eval gamma=helperCurve c2 gamma index := by
  simp only [helperPolynomial,eval_finsetSum,eval_monomial,helperCurve]
  apply Finset.sum_congr rfl
  intro lane _
  exact mul_comm _ _

theorem split_sum (values : Fin 29 → K) (gamma : K) :
    (∑ lane : Fin 29, gamma^lane.val*values lane)=
      lowClaims values gamma+gamma^26*helperClaims values gamma := by
  have concatenated := FiniteSumConcat.concat 26 3
    (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat (SimplexCategory.mk 28))
    (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat (SimplexCategory.mk 25))
    (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat (SimplexCategory.mk 2))
    (fun lane : Fin 29 => gamma^lane.val*values lane)
  simp only [Fin.val_castAdd,Fin.val_natAdd] at concatenated
  have right : (∑ lane : Fin 3, gamma^(26+lane.val)*values (Fin.natAdd 26 lane))=
      gamma^26*helperClaims values gamma := by
    unfold helperClaims
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lane _
    rw [pow_add,mul_assoc]
  rw [right] at concatenated
  exact concatenated

theorem encode_c1Batch (p : C1Messages) (gamma : K) (index : Fin 1048576) :
    exactInitialEncoder (c1Batch p gamma) index=
      ∑ lane : Fin 26, gamma^lane.val*exactInitialEncoder (p lane) index := by
  change initialLinear (c1Batch p gamma) index=_
  rw [c1Batch,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,initialLinear_apply]

theorem received_left (p : C1Messages) (c2 : C2Received) (lane : Fin 26)
    (index : Fin 1048576) :
    received29 (exactC1 p) c2 (Fin.castAdd 3 lane) index=exactInitialEncoder (p lane) index := by
  simp only [received29,Fin.val_castAdd,dif_pos lane.isLt,exactC1]

theorem received_right (p : C1Messages) (c2 : C2Received) (lane : Fin 3)
    (index : Fin 1048576) :
    received29 (exactC1 p) c2 (Fin.natAdd 26 lane) index=c2 lane index := by
  have notLeft : ¬ 26+lane.val<26 := by omega
  simp only [received29,Fin.val_natAdd,dif_neg notLeft,Nat.add_sub_cancel_left]

/-- The literal selected 26+3 scalar-power batch, not a new toy curve. -/
theorem raw_batch_split (p : C1Messages) (c2 : C2Received) (gamma : K)
    (index : Fin 1048576) :
    rawBatch (exactC1 p) c2 gamma index=
      exactInitialEncoder (c1Batch p gamma) index+gamma^26*helperCurve c2 gamma index := by
  rw [rawBatch,split_sum,encode_c1Batch]
  simp only [lowClaims,helperClaims,helperCurve,received_left,received_right]

/-- The same reduction is local to genuine C1 agreement. Errors in received
C1 outside this index are neither assumed absent nor silently polynomial. -/
theorem raw_batch_on_c1_support (received : C1Received) (p : C1Messages)
    (c2 : C2Received) (gamma : K) (index : Fin 1048576)
    (same : ∀ lane, received lane index=exactInitialEncoder (p lane) index) :
    rawBatch received c2 gamma index=rawBatch (exactC1 p) c2 gamma index := by
  unfold rawBatch
  apply Finset.sum_congr rfl
  intro lane _
  unfold received29
  split
  · rw [same]
    rfl
  · rfl

def normalized (p : C1Messages) (gamma : K) (message : Message) : Message :=
  (gamma^26)⁻¹ • (message-c1Batch p gamma)

theorem encode_normalized (p : C1Messages) (gamma : K) (message : Message)
    (index : Fin 1048576) :
    exactInitialEncoder (normalized p gamma message) index=
      (gamma^26)⁻¹*(exactInitialEncoder message index-exactInitialEncoder (c1Batch p gamma) index) := by
  change initialLinear (normalized p gamma message) index=_
  simp only [normalized,map_smul,map_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,initialLinear_apply]

/-- Affine subtraction/scaling preserves every individual stored-symbol
agreement, so it preserves arbitrary complete-fibre supports as well. -/
theorem agreement_iff (p : C1Messages) (c2 : C2Received) (gamma : K)
    (nonzero : gamma≠0) (message : Message) (index : Fin 1048576) :
    rawBatch (exactC1 p) c2 gamma index=exactInitialEncoder message index ↔
      helperCurve c2 gamma index=exactInitialEncoder (normalized p gamma message) index := by
  rw [raw_batch_split,encode_normalized]
  have nz : gamma^26≠0 := pow_ne_zero _ nonzero
  constructor
  · intro h
    apply (mul_left_cancel₀ nz)
    rw [mul_inv_cancel_left₀ nz]
    exact eq_sub_of_add_eq' h
  · intro h
    have multiplied := congrArg (fun z : K => gamma^26*z) h
    rw [mul_inv_cancel_left₀ nz] at multiplied
    exact add_eq_of_eq_sub' multiplied

theorem support_iff (p : C1Messages) (c2 : C2Received) (gamma : K)
    (nonzero : gamma≠0) (message : Message) (S : Finset (Fin 262144)) :
    (∀ f∈S, ∀ slot : Fin 4,
      rawBatch (exactC1 p) c2 gamma (fibreEmbed (f,slot))=
        exactInitialEncoder message (fibreEmbed (f,slot))) ↔
    (∀ f∈S, ∀ slot : Fin 4,
      helperCurve c2 gamma (fibreEmbed (f,slot))=
        exactInitialEncoder (normalized p gamma message) (fibreEmbed (f,slot))) := by
  constructor
  · intro h f hf slot
    exact (agreement_iff p c2 gamma nonzero message _).mp (h f hf slot)
  · intro h f hf slot
    exact (agreement_iff p c2 gamma nonzero message _).mpr (h f hf slot)

/-- A fixed C1 own-support can be used without replacing the received word
globally by its candidate. No agreement is asserted on the excluded fibres. -/
theorem restricted_support_iff (received : C1Received) (p : C1Messages)
    (c2 : C2Received) (gamma : K) (nonzero : gamma≠0) (message : Message)
    (S : Finset (Fin 262144))
    (same : ∀ f∈S, ∀ slot : Fin 4, ∀ lane : Fin 26,
      received lane (fibreEmbed (f,slot))=exactInitialEncoder (p lane) (fibreEmbed (f,slot))) :
    (∀ f∈S, ∀ slot : Fin 4,
      rawBatch received c2 gamma (fibreEmbed (f,slot))=
        exactInitialEncoder message (fibreEmbed (f,slot))) ↔
    (∀ f∈S, ∀ slot : Fin 4,
      helperCurve c2 gamma (fibreEmbed (f,slot))=
        exactInitialEncoder (normalized p gamma message) (fibreEmbed (f,slot))) := by
  constructor
  · intro h f hf slot
    apply (agreement_iff p c2 gamma nonzero message _).mp
    rw [← raw_batch_on_c1_support received p c2 gamma _ (same f hf slot)]
    exact h f hf slot
  · intro h f hf slot
    rw [raw_batch_on_c1_support received p c2 gamma _ (same f hf slot)]
    exact (agreement_iff p c2 gamma nonzero message _).mpr (h f hf slot)

def c1Error (ell : Message →ₗ[K] K) (p : C1Messages) (claims : Fin 29 → K) : K[X] :=
  ∑ lane : Fin 26, monomial lane.val (claims (Fin.castAdd 3 lane)-ell (p lane))

theorem c1Error_degree (ell : Message →ₗ[K] K) (p : C1Messages) (claims : Fin 29 → K) :
    (c1Error ell p claims).natDegree≤25 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro lane _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem c1Error_eval (ell : Message →ₗ[K] K) (p : C1Messages)
    (claims : Fin 29 → K) (gamma : K) :
    (c1Error ell p claims).eval gamma=lowClaims claims gamma-ell (c1Batch p gamma) := by
  simp only [c1Error,eval_finsetSum,eval_monomial,lowClaims,c1Batch,map_sum,map_smul,smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro lane _
  ring

/-- Ordinary MLE rows and the two natural-circle OOD rows are linear
functionals. For either kind, the fixed C1 error is retained explicitly;
normalizing the received helper curve does not remove false C1 claims. -/
theorem claim_residual (ell : Message →ₗ[K] K) (p : C1Messages)
    (claims : Fin 29 → K) (gamma : K) (nonzero : gamma≠0) (message : Message) :
    (∑ lane : Fin 29, gamma^lane.val*claims lane)-ell message=
      (c1Error ell p claims).eval gamma+
        gamma^26*(helperClaims claims gamma-ell (normalized p gamma message)) := by
  have nz : gamma^26≠0 := pow_ne_zero _ nonzero
  rw [split_sum,c1Error_eval]
  simp only [normalized,map_smul,map_sub,smul_eq_mul]
  rw [mul_sub,mul_inv_cancel_left₀ nz]
  ring

theorem scaled_claim_residual (ell : Message →ₗ[K] K) (p : C1Messages)
    (claims : Fin 29 → K) (gamma : K) (nonzero : gamma≠0) (message : Message) :
    (gamma^26)⁻¹*((∑ lane : Fin 29, gamma^lane.val*claims lane)-ell message)=
      (gamma^26)⁻¹*(c1Error ell p claims).eval gamma+
        (helperClaims claims gamma-ell (normalized p gamma message)) := by
  rw [claim_residual ell p claims gamma nonzero message,mul_add,
    inv_mul_cancel_left₀ (pow_ne_zero 26 nonzero)]

#print axioms raw_batch_split
#print axioms raw_batch_on_c1_support
#print axioms helperPolynomial_degree
#print axioms helperPolynomial_eval
#print axioms encode_normalized
#print axioms agreement_iff
#print axioms support_iff
#print axioms restricted_support_iff
#print axioms c1Error_degree
#print axioms c1Error_eval
#print axioms claim_residual
#print axioms scaled_claim_residual
end
end AspisV8.FixedC1HelperReduction
