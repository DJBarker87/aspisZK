import CausalOrderedRelation
import CanonicalRelationInput

/-! Typed source-shaped compact recurrence with the deferred image terminal.
No Rust execution, transcript equality, authenticated-word construction, or
challenge law is asserted. Decoded response buffers have causal function
types; final256 remains adaptive after alpha0 and before the query schedule.
The shifted ordinary functional is a Before input, not reconstructed here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000
namespace AspisV8.TypedRelationTerminal
open Finset
open AspisV5FriRelationCandidateBridge AspisV5ComponentCConcreteFoldLinearity
open AspisV8.OptimizedRelationRefinement AspisV8.PostQueryFunctional
open AspisV8.FirstImageDiscrepancy AspisV8.CausalOrderedRelation
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- Narrow port of V5RelationStressSourceBridge.dualWeightFoldLayer_add;
no extra V7 schedule or cache import is needed for this four-term identity. -/
theorem fold_add (n : Nat) (a : K) (w v : Fin (4*n) → K) :
    dualWeightFoldLayer n a (fun i => w i+v i) =
      fun i => dualWeightFoldLayer n a w i+dualWeightFoldLayer n a v i := by
  funext i
  unfold dualWeightFoldLayer dualWeightFoldValue
  ring

def lastWeight (n : Nat) (v : K) : Fin n → K :=
  fun i => if i.val+1=n then v else 0

/-- Symbolic last-index transport, valid for every layer size. -/
theorem last_fold (n : Nat) (a v : K) :
    dualWeightFoldLayer n a (lastWeight (4*n) v)=lastWeight n (v*a/4) := by
  funext i
  have h0 : 4*i.val+0+1≠4*n := by omega
  have h1 : 4*i.val+1+1≠4*n := by omega
  have h2 : 4*i.val+2+1≠4*n := by omega
  change ((if 4*i.val+0+1=4*n then v else 0) +
    a^3*(if 4*i.val+1+1=4*n then v else 0) +
    a^2*(if 4*i.val+2+1=4*n then v else 0) +
    a*(if 4*i.val+3+1=4*n then v else 0))/4 =
      if i.val+1=n then v*a/4 else 0
  rw [if_neg h0, if_neg h1, if_neg h2]
  by_cases h : i.val+1=n
  · have h3 : 4*i.val+3+1=4*n := by omega
    simp only [if_pos h3, if_pos h, mul_zero, zero_add]
    ring
  · have h3 : 4*i.val+3+1≠4*n := by omega
    simp only [if_neg h3, if_neg h, mul_zero, zero_add, zero_div]

def firstImage (tau b c a0 : K) : K :=
  dualWeightFoldValue a0 ![0,-tau^2*c,tau^2*b,tau]

/-- Only one four-entry block is expanded. No 1024-entry sum or vector is
enumerated: all other blocks vanish by their index bounds. -/
theorem image_first_fold (w : Fin 1024 → K) (tau b c a0 : K) :
    dualWeightFoldLayer 256 a0
      (ImageCallbackInterfaces.imageWeights w ⟨1023, by decide⟩ ⟨1022, by decide⟩
        ⟨1021, by decide⟩ tau b c) =
      fun i => dualWeightFoldLayer 256 a0 w i +
        lastWeight 256 (firstImage tau b c a0) i := by
  funext i
  by_cases h : i.val+1=256
  · have hi : i=⟨255, by decide⟩ :=
      Fin.ext (show i.val=255 by omega)
    subst i
    simp [dualWeightFoldLayer, dualWeightFoldValue,
      ImageCallbackInterfaces.imageWeights, childIndex, lastWeight, firstImage]
    <;> ring
  · have absent (j : Fin 4) : childIndex i j ≠ (⟨1023, by decide⟩ : Fin 1024) ∧
        childIndex i j ≠ (⟨1022, by decide⟩ : Fin 1024) ∧
        childIndex i j ≠ (⟨1021, by decide⟩ : Fin 1024) := by
      have hi := i.isLt
      have hj := j.isLt
      simp only [ne_eq, Fin.ext_iff, childIndex_val]
      omega
    simp only [dualWeightFoldLayer, dualWeightFoldValue,
      ImageCallbackInterfaces.imageWeights,
      if_neg (absent 0).1, if_neg (absent 0).2.1, if_neg (absent 0).2.2,
      if_neg (absent 1).1, if_neg (absent 1).2.1, if_neg (absent 1).2.2,
      if_neg (absent 2).1, if_neg (absent 2).2.1, if_neg (absent 2).2.2,
      if_neg (absent 3).1, if_neg (absent 3).2.1, if_neg (absent 3).2.2,
      lastWeight, if_neg h, add_zero, sub_zero]

def tailDual (w : Fin 256 → K) (a1 a2 a3 : K) : Fin 4 → K :=
  dualWeightFoldLayer 4 a3 (dualWeightFoldLayer 16 a2 (dualWeightFoldLayer 64 a1 w))
def tailPrimal (f : Fin 256 → K) (a1 a2 a3 : K) : Fin 4 → K :=
  coefficientFoldLayer 4 a3 (coefficientFoldLayer 16 a2 (coefficientFoldLayer 64 a1 f))
def ordinaryTerminal (p : Prefix (K := K)) (a1 a2 a3 : K) : Fin 4 → K :=
  tailDual (dualWeightFoldLayer 256 p.alpha0 p.ordinary) a1 a2 a3
def queryWeights {q : Nat} (points : Fin q → K) (rho : K) : Fin 256 → K :=
  fun i => ∑ j, rho^(j.val+1)*lineWeight (points j) i
def imageTerminal (tau b c a0 a1 a2 a3 : K) : K :=
  (a1*a2*a3/256)*(tau*a0+tau^2*(b*a0^2-c*a0^3))

theorem tail_add (w v : Fin 256 → K) (a1 a2 a3 : K) :
    tailDual (fun i => w i+v i) a1 a2 a3 =
      fun i => tailDual w a1 a2 a3 i+tailDual v a1 a2 a3 i := by
  simp only [tailDual, fold_add]

theorem tail_last (v a1 a2 a3 : K) :
    tailDual (lastWeight 256 v) a1 a2 a3 =
      lastWeight 4 (((v*a1/4)*a2/4)*a3/4) := by
  unfold tailDual
  rw [last_fold, last_fold, last_fold]

theorem candidate_add {n : Nat} (w v f : Fin n → K) :
    candidateClaim (fun i => w i+v i) f=candidateClaim w f+candidateClaim v f := by
  simp only [candidateClaim, mul_add, Finset.sum_add_distrib]

theorem last_dot (v : K) (f : Fin 4 → K) :
    candidateClaim (lastWeight 4 v) f=v*f 3 := by
  simp [candidateClaim, lastWeight, Fin.sum_univ_four, mul_comm]

/-- The structured evaluator can defer the three query folds and all four
ordinary folds, carrying only this scalar image contribution at final[3].
Query weights never undergo the chord or alpha0 fold. -/
theorem post_terminal {q : Nat} (p : Prefix (K := K)) (points : Fin q → K)
    (rho a1 a2 a3 : K) (f : Fin 4 → K) :
    candidateClaim (tailDual (postWeights p points rho) a1 a2 a3) f =
      candidateClaim (fun i => ordinaryTerminal p a1 a2 a3 i+
        tailDual (queryWeights points rho) a1 a2 a3 i) f +
      imageTerminal p.tau p.b p.c p.alpha0 a1 a2 a3*f 3 := by
  have first : postWeights p points rho = fun i =>
      (dualWeightFoldLayer 256 p.alpha0 p.ordinary i+
        lastWeight 256 (firstImage p.tau p.b p.c p.alpha0) i)+
      queryWeights points rho i := by
    funext i
    exact congrArg (fun weight : Fin 256 → K => weight i+queryWeights points rho i)
      (image_first_fold p.ordinary p.tau p.b p.c p.alpha0)
  have coefficient := ImageCallbackInterfaces.sparse_image_terminal
    p.tau p.b p.c p.alpha0 a1 a2 a3
  change (((firstImage p.tau p.b p.c p.alpha0*a1/4)*a2/4)*a3/4) =
    imageTerminal p.tau p.b p.c p.alpha0 a1 a2 a3 at coefficient
  have weights : tailDual (postWeights p points rho) a1 a2 a3 = fun i =>
      (ordinaryTerminal p a1 a2 a3 i+tailDual (queryWeights points rho) a1 a2 a3 i)+
      lastWeight 4 (imageTerminal p.tau p.b p.c p.alpha0 a1 a2 a3) i := by
    rw [first, tail_add, tail_add, tail_last, coefficient]
    funext i
    simp only [ordinaryTerminal]
    ring
  rw [weights, candidate_add, last_dot]

/-- Exactly three decoded responses, each fixed before its own challenge. -/
structure TailFields where
  first : Sent K
  second : K → Sent K
  third : K → K → Sent K

def TailFields.raw (t : TailFields (K := K)) : RawRounds (K := K) 3 256 :=
  .step t.first (fun a1 => .step (t.second a1)
    (fun a2 => .step (t.third a1 a2) (fun _ => .done 4)))

def terminalClaim {q : Nat} (p : Prefix (K := K)) (points : Fin q → K)
    (received : K → K) (rho : K) (t : TailFields (K := K)) (a1 a2 a3 : K) : K :=
  sourceHorner p.quarter
    (sourceHorner p.quarter
      (sourceHorner p.quarter (postClaim p points received rho) t.first a1)
      (t.second a1) a2) (t.third a1 a2) a3

def sourceAccepts {q : Nat} (p : Prefix (K := K)) (final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) (rho : K)
    (t : TailFields (K := K)) (a1 a2 a3 : K) : Prop :=
  let f := tailPrimal final a1 a2 a3
  candidateClaim (fun i => ordinaryTerminal p a1 a2 a3 i+
    tailDual (queryWeights points rho) a1 a2 a3 i) f +
    imageTerminal p.tau p.b p.c p.alpha0 a1 a2 a3*f 3 =
      terminalClaim p points received rho t a1 a2 a3

/-- Source PLUS injection, ordered rho powers, and exact compact response0.
No vanishing residual or image-validity hypothesis is supplied. -/
theorem first_claim_horner {q : Nat} (p : Prefix (K := K))
    (points : Fin q → K) (received : K → K) (rho : K) :
    postClaim p points received rho =
      sourceHorner p.quarter p.claim p.response0 p.alpha0+
        ∑ j, rho^(j.val+1)*received (points j) := by
  unfold postClaim Prefix.carried increment
  rw [nextClaim_source_horner]

theorem tail_accepts_iff {q : Nat} (p : Prefix (K := K)) (final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) (rho : K)
    (t : TailFields (K := K)) (a1 a2 a3 : K) :
    t.raw.accepts p.quarter (postWeights p points rho) final
      (postClaim p points received rho) [a1,a2,a3] ↔
      sourceAccepts p final points received rho t a1 a2 a3 := by
  change candidateClaim (tailDual (postWeights p points rho) a1 a2 a3)
    (tailPrimal final a1 a2 a3) =
    nextClaim p.quarter (nextClaim p.quarter
      (nextClaim p.quarter (postClaim p points received rho) t.first a1)
      (t.second a1) a2) (t.third a1 a2) a3 ↔ _
  rw [post_terminal]
  simp only [sourceAccepts, terminalClaim, nextClaim_source_horner]

/-- Typed source-facing strategy. In particular final has no query/rho input;
the three later response functions receive previous, never future, alphas. -/
structure Fields (D : Finset K) (q : Nat) where
  firstResponse : K → Sent K
  final : K → K → Fin 256 → K
  later : K → K → OrderedQueryGame.Schedule D q → K → TailFields (K := K)

def Fields.strategy {D : Finset K} {q : Nat} (fields : Fields D q) : Strategy D q where
  firstResponse := fields.firstResponse
  final := fields.final
  rawTail := fun tau alpha queries rho => (fields.later tau alpha queries rho).raw

variable [NeZero (2 : K)]

/-- Exact constructed acceptance equality. It says nothing about whether a
particular Rust transcript supplies these typed fields or fresh challenges. -/
theorem source_accepts_iff {D B : Finset K} {q : Nat} (pre : Before (K := K))
    (oracle : FixedOracle D B pre.referenceQ) (fields : Fields D q)
    (tau alpha : K) (queries : OrderedQueryGame.Schedule D q) (rho a1 a2 a3 : K) :
    sourceAccepts (pre.snapshot tau (fields.firstResponse tau) alpha)
      (fields.final tau alpha) (fun j => (queries j : K)) (oracle.folded alpha) rho
      (fields.later tau alpha queries rho) a1 a2 a3 ↔
    CausalOrderedRelation.accepts pre oracle fields.strategy tau alpha queries rho [a1,a2,a3] := by
  exact (tail_accepts_iff (pre.snapshot tau (fields.firstResponse tau) alpha)
    (fields.final tau alpha) (fun j => (queries j : K)) (oracle.folded alpha) rho
    (fields.later tau alpha queries rho) a1 a2 a3).symm

end

namespace Decoded
noncomputable section
abbrev K := CanonicalRelationInput.K

/-- Each buffer belongs to its own causal history. They need not be equal
across histories; this is not an embedding of one wire as a constant strategy. -/
def fields {D : Finset K} {q : Nat}
    (response0 : K → List K) (final256 : K → K → List K)
    (response1 : K → K → OrderedQueryGame.Schedule D q → K → List K)
    (response2 : K → K → OrderedQueryGame.Schedule D q → K → K → List K)
    (response3 : K → K → OrderedQueryGame.Schedule D q → K → K → K → List K) :
    Fields D q where
  firstResponse := fun tau => CanonicalRelationInput.response (response0 tau) 0
  final := fun tau alpha i => (final256 tau alpha).getD (441+i.val) 0
  later := fun tau alpha queries rho =>
    { first := CanonicalRelationInput.response (response1 tau alpha queries rho) 1
      second := fun a1 => CanonicalRelationInput.response (response2 tau alpha queries rho a1) 2
      third := fun a1 a2 => CanonicalRelationInput.response (response3 tau alpha queries rho a1 a2) 3 }

/-- The source's six stored fields, including missing-quartic convention,
are reused from the checked 697-field projection, not old V7 offsets. -/
theorem response_fields (values : List K) (round : Fin 4) (j : Fin 6) :
    (CanonicalRelationInput.response values round).sent j=
      values.getD (417+6*round.val+j.val) 0 :=
  CanonicalRelationInput.response_sent values round j

/-- No buffer shape or canonicality is inferred here: parse_success and
decoded_response/decoded_final remain the separate typed-parser boundary. -/
theorem compact_boundary (values : List K) (round : Fin 4) (quarter claim : K)
    (checked : quarter*4=1) :
    JointImageGame.boundary (claimed quarter claim (CanonicalRelationInput.response values round))=claim :=
  CanonicalRelationInput.decoded_boundary values round quarter claim checked
end
end Decoded

#print axioms last_fold
#print axioms image_first_fold
#print axioms post_terminal
#print axioms first_claim_horner
#print axioms tail_accepts_iff
#print axioms source_accepts_iff
#print axioms Decoded.response_fields
#print axioms Decoded.compact_boundary
end AspisV8.TypedRelationTerminal
