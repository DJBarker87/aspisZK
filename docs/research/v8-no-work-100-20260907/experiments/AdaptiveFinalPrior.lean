import PostQueryFunctional

/-! Permanent far-final regression. After alpha0 the actual folded functional
is known. A nonzero coordinate permits one legal final coefficient to repair
the carried prior, even if a fixed-reference discrepancy was nonzero.
This does not preserve query agreement, supply a payment witness, or establish
an accepting proof. The exact query-residual change is retained below. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.AdaptiveFinalPrior
noncomputable section
open Polynomial AspisV8.PostQueryFunctional
open AspisV5FriRelationCandidateBridge AspisV5FriConcreteEncoderApplicability
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2:K)]

theorem dot_single_update {n : Nat} (w f : Fin n → K) (j : Fin n) (delta : K) :
    candidateClaim w (f+Pi.single j delta)=candidateClaim w f+delta*w j := by
  classical
  simp [candidateClaim,Pi.add_apply,add_mul,Finset.sum_add_distrib,
    Pi.single_apply,ite_mul]

def correction (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256) : K :=
  p.prior f/p.foldWeight j

def corrected (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256) : Fin 256 → K :=
  f+Pi.single j (correction p f j)

theorem corrected_at (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256) :
    corrected p f j j=f j+correction p f j := by
  simp [corrected]

theorem corrected_away (p : Prefix (K:=K)) (f : Fin 256 → K) (j i : Fin 256)
    (different : i≠j) : corrected p f j i=f i := by
  simp [corrected,Pi.single_apply,Ne.symm different]

/-- `p` is the actual post-alpha prefix. The correction uses only that
prefix and f, not any future query, rho, or later-round challenge. -/
theorem corrected_prior_zero (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256)
    (nonzero : p.foldWeight j≠0) : p.prior (corrected p f j)=0 := by
  unfold Prefix.prior corrected
  rw [dot_single_update]
  have h : correction p f j*p.foldWeight j=p.prior f :=
    div_mul_cancel₀ _ nonzero
  rw [h]
  unfold Prefix.prior
  ring

/-- The scalar repair is still a syntactically legal degree-255 final; it
does not add coefficients or replace the selected final256 grammar. -/
theorem corrected_degree (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256) :
    (naturalCoefficientPolynomial (corrected p f j)).natDegree≤255 :=
  naturalCoefficientPolynomial_natDegree_le (by decide) _

theorem corrected_ne (p : Prefix (K:=K)) (f : Fin 256 → K) (j : Fin 256)
    (nonzero : p.foldWeight j≠0) (wrong : p.prior f≠0) : corrected p f j≠f := by
  intro same
  apply wrong
  rw [←same]
  exact corrected_prior_zero p f j nonzero

/-- This is the obstruction, with the modified coordinate made explicit.
The nonzero incoming discrepancy is NOT claimed to survive adaptive finals. -/
theorem exists_adaptive_prior_zero (p : Prefix (K:=K)) (f : Fin 256 → K)
    (j : Fin 256) (nonzero : p.foldWeight j≠0) :
    ∃ final : Fin 256 → K,
      p.prior final=0 ∧
      final j=f j+p.prior f/p.foldWeight j ∧
      (∀ i : Fin 256,i≠j → final i=f i) ∧
      (naturalCoefficientPolynomial final).natDegree≤255 := by
  refine ⟨corrected p f j,corrected_prior_zero p f j nonzero,corrected_at p f j,?_,
    corrected_degree p f j⟩
  intro i hi
  exact corrected_away p f j i hi

/-- Repairing the relation prior changes the actual query residual by the
corresponding natural basis value. It does not promise any matching set. -/
theorem corrected_query_residual {q : Nat} (p : Prefix (K:=K)) (f : Fin 256 → K)
    (j : Fin 256) (points : Fin q → K) (received : K → K) (i : Fin q) :
    PostQueryFunctional.residual (corrected p f j) points received i=
      PostQueryFunctional.residual f points received i+correction p f j*lineWeight (points i) j := by
  unfold PostQueryFunctional.residual
  rw [lineEval_dot,lineEval_dot]
  unfold corrected
  rw [dot_single_update]
  ring

#print axioms dot_single_update
#print axioms corrected_at
#print axioms corrected_away
#print axioms corrected_prior_zero
#print axioms corrected_degree
#print axioms corrected_ne
#print axioms exists_adaptive_prior_zero
#print axioms corrected_query_residual
end
end AspisV8.AdaptiveFinalPrior
