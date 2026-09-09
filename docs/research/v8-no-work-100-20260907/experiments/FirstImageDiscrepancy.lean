import PostQueryFunctional

/-! Construct the pre-tau image discrepancy and first compact response error.
All public-functional inputs and the reference Q belong to Before. A causal
caller chooses response0 as a function of tau, then supplies alpha0 to snapshot.
No polynomiality of an arbitrary received word, image validity, successful
recovery, or boundary correspondence equality is a constructor premise. -/
set_option autoImplicit false
namespace AspisV8.FirstImageDiscrepancy
open Polynomial
open AspisV5FriRelationCandidateBridge AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderApplicability
open AspisV8.JointImageGame AspisV8.OptimizedRelationRefinement
open AspisV8.PostQueryFunctional
universe u
variable {K : Type u} [Field K] [DecidableEq K]

/-- A static public/reference prefix fixed before tau. It deliberately has
no tau, response0, alpha0, final, query schedule or rho field. -/
structure Before where
  ordinary : Fin 1024 → K
  referenceQ : Fin 1024 → K
  claim : K
  quarter : K
  b : K
  c : K

def Before.prior (p : Before (K := K)) : K :=
  p.claim-candidateClaim p.ordinary p.referenceQ
def Before.E1 (p : Before (K := K)) : K := p.referenceQ ⟨1023, by decide⟩
def Before.E2 (p : Before (K := K)) : K :=
  p.b*p.referenceQ ⟨1022, by decide⟩-p.c*p.referenceQ ⟨1021, by decide⟩
def Before.imageWeight (p : Before (K := K)) (tau : K) : Fin 1024 → K :=
  ImageCallbackInterfaces.imageWeights p.ordinary
    ⟨1023, by decide⟩ ⟨1022, by decide⟩ ⟨1021, by decide⟩ tau p.b p.c
noncomputable def Before.errorPolynomial (p : Before (K := K)) : K[X] :=
  imagePolynomial p.prior p.E1 p.E2

/-- Three scalar coefficients only; no expansion of the 1024-vector. -/
theorem imagePolynomial_eval (prior e1 e2 tau : K) :
    (imagePolynomial prior e1 e2).eval tau = prior-tau*e1-tau^2*e2 := by
  simp [imagePolynomial, monomialPolynomial, Fin.sum_univ_succ]
  ring

/-- Actual scalar-minus-dot for the carried image functional. The two image
claims are zero claims; the ordinary scalar is unchanged. -/
theorem error_eval (p : Before (K := K)) (tau : K) :
    p.errorPolynomial.eval tau = p.claim-candidateClaim (p.imageWeight tau) p.referenceQ := by
  have h := ImageCallbackInterfaces.image_boundary p.ordinary p.referenceQ
    ⟨1023, by decide⟩ ⟨1022, by decide⟩ ⟨1021, by decide⟩ p.claim tau p.b p.c
  simpa only [Before.errorPolynomial, Before.prior, Before.E1, Before.E2,
    Before.imageWeight, candidateClaim, imagePolynomial_eval] using h.symm

theorem error_degree (p : Before (K := K)) : p.errorPolynomial.natDegree ≤ 2 :=
  image_degree p.prior p.E1 p.E2

theorem error_nonzero (p : Before (K := K)) (invalid : p.E1 ≠ 0 ∨ p.E2 ≠ 0) :
    p.errorPolynomial ≠ 0 := image_nonzero p.prior p.E1 p.E2 invalid

noncomputable def Before.firstError (p : Before (K := K)) (tau : K) (sent : Sent K) : K[X] :=
  discrepancy 256 p.quarter p.claim sent (p.imageWeight tau) p.referenceQ

theorem firstError_degree (p : Before (K := K)) (tau : K) (sent : Sent K) :
    (p.firstError tau sent).natDegree ≤ 6 :=
  discrepancy_degree 256 p.quarter p.claim sent (p.imageWeight tau) p.referenceQ

/-- The six arbitrary response fields need no supplied boundary certificate.
The compact quartic reconstruction derives this equality. -/
theorem firstError_boundary (p : Before (K := K)) (hq : p.quarter*4=1)
    (tau : K) (sent : Sent K) :
    boundary (p.firstError tau sent)=p.errorPolynomial.eval tau := by
  unfold Before.firstError
  rw [discrepancy_boundary 256 p.quarter p.claim sent (p.imageWeight tau) p.referenceQ hq]
  exact (error_eval p tau).symm

theorem firstError_nonzero (p : Before (K := K)) (hq : p.quarter*4=1)
    (tau : K) (sent : Sent K) (wrong : p.errorPolynomial.eval tau ≠ 0) :
    p.firstError tau sent ≠ 0 :=
  boundary_ne_zero _ _ (firstError_boundary p hq tau sent) wrong

/-- Called after alpha0. A caller using firstResponse : K -> Sent K fixes
the response at firstResponse tau before alpha0; snapshot itself does not
assert that any particular byte transcript obeyed that timing. -/
def Before.snapshot (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    PostQueryFunctional.Prefix (K := K) where
  ordinary := p.ordinary
  referenceQ := p.referenceQ
  claim := p.claim
  quarter := p.quarter
  tau := tau
  b := p.b
  c := p.c
  alpha0 := alpha
  response0 := sent

theorem snapshot_imageWeight (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    (p.snapshot tau sent alpha).imageWeight=p.imageWeight tau := rfl

theorem snapshot_referenceFinal (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    (p.snapshot tau sent alpha).referenceFinal=coefficientFoldLayer 256 alpha p.referenceQ := rfl

theorem snapshot_carried (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    (p.snapshot tau sent alpha).carried=nextClaim p.quarter p.claim sent alpha := rfl

theorem snapshot_trueError (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    (p.snapshot tau sent alpha).trueError=(p.firstError tau sent).eval alpha := rfl

/-- Actual compact evaluation minus the exact folded dot. This is stronger
than merely assigning the old abstract game a field named trueError. -/
theorem firstError_eval (p : Before (K := K)) (tau : K) (sent : Sent K) (alpha : K) :
    (p.firstError tau sent).eval alpha =
      (p.snapshot tau sent alpha).carried-candidateClaim
        (p.snapshot tau sent alpha).foldWeight (p.snapshot tau sent alpha).referenceFinal :=
  discrepancy_eval 256 p.quarter p.claim sent (p.imageWeight tau) p.referenceQ alpha

#print axioms imagePolynomial_eval
#print axioms error_eval
#print axioms error_degree
#print axioms error_nonzero
#print axioms firstError_degree
#print axioms firstError_boundary
#print axioms firstError_nonzero
#print axioms snapshot_imageWeight
#print axioms snapshot_referenceFinal
#print axioms snapshot_carried
#print axioms snapshot_trueError
#print axioms firstError_eval
end AspisV8.FirstImageDiscrepancy
