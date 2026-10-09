import SelectedQuotientOriginal

/-! Source-shaped obstruction to treating the normalized virtual quotient as
a fixed quadratic helper curve before C1 OOD claims have been bound. The
received C1/C2 words here are zero; both lane-zero OOD answers are one, fixed
before gamma. This is a legal algebraic prefix, not a payment or acceptance
construction. The correct alternative is raw original-code normalization on
the actual C1 own support, with lost support charged explicitly. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 20000
namespace AspisV8.QuotientHelperShift
noncomputable section
open Polynomial Finset

section Generic
variable {F : Type*} [Field F] [DecidableEq F]

def cleared (a : F) (p : F[X]) : F[X] := X^26*p-C a

theorem cleared_nonzero (a : F) (ha : a≠0) (p : F[X]) : cleared a p≠0 := by
  intro h
  have h0 := congrArg (fun r : F[X] => r.eval 0) h
  simp only [cleared,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_zero,
    zero_pow (by decide : 26≠0),zero_mul,zero_sub,neg_eq_zero] at h0
  exact ha h0

theorem cleared_degree (a : F) (p : F[X]) (degree : p.natDegree≤2) :
    (cleared a p).natDegree≤28 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · have h : ((X^26 : F[X])*p).natDegree≤(X^26 : F[X]).natDegree+p.natDegree :=
      Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_X_pow] at h
    exact h.trans (by omega)
  · simp only [Polynomial.natDegree_C]; omega

/-- Any putative quadratic agrees with a nonzero reciprocal 26th power at
at most 28 nonzero parameters. This is a symbolic root count over any field,
not enumeration of QM31 or a fixed-target security bound. -/
theorem inverse_shift_card (a : F) (ha : a≠0) (p : F[X])
    (degree : p.natDegree≤2) (G : Finset F) :
    (G.filter fun gamma => gamma≠0 ∧ p.eval gamma=(gamma^26)⁻¹*a).card≤28 := by
  apply (Polynomial.card_le_degree_of_subset_roots (p := cleared a p) ?_).trans
    (cleared_degree a p degree)
  intro gamma hg
  obtain ⟨nonzero,same⟩ := (Finset.mem_filter.mp hg).2
  apply (Polynomial.mem_roots (cleared_nonzero a ha p)).mpr
  change (cleared a p).eval gamma=0
  simp only [cleared,eval_sub,eval_mul,eval_pow,eval_X,eval_C,same,
    mul_inv_cancel_left₀ (pow_ne_zero 26 nonzero),sub_self]
end Generic

open AspisV8.OODInterpolant AspisV8.SelectedQuotientOriginal
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5FriInitialCircleEncoderIdentity
open AspisV8.ChordPolynomialImage
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Identical lane-zero claims at both actual OOD positions. All other
claims, including the three helper claims, are zero. Coordinates and the
checked inverse are left untouched; only gamma varies afterwards. -/
def falseData (d : Data (K := K)) (gamma : K) : Data (K := K) :=
  { d with gamma := gamma, answers := fun _ => Pi.single 0 1 }

theorem falseData_checked (d : Data (K := K)) (gamma : K) :
    (falseData d gamma).Checked ↔ d.Checked := Iff.rfl

theorem falseData_batch (d : Data (K := K)) (gamma : K) (r : Fin 2) :
    (falseData d gamma).batch r=1 := by
  simp [Data.batch,falseData,Pi.single_apply]

theorem falseData_interpolant (d : Data (K := K)) (gamma : K) :
    (falseData d gamma).interpolant=vector d.useX 1 0 := by
  simp only [Data.interpolant,Data.intercept,Data.slope,
    falseData_batch,OODInterpolant.intercept,OODInterpolant.slope,sub_self,zero_mul,sub_zero]
  rfl

theorem falseData_encoded (d : Data (K := K)) (gamma : K)
    (i : Fin 1048576) : exactInitialEncoder (falseData d gamma).interpolant i=1 := by
  rw [falseData_interpolant]
  change circleEval (initialP0 (vector d.useX 1 0))
    (initialP1 (vector d.useX 1 0)) (symbolX i) (symbolY i)=1
  rw [vector_eval]
  simp only [zero_mul,add_zero]

theorem falseData_virtual (d : Data (K := K)) (gamma : K)
    (i : Fin 1048576) : virtual (falseData d gamma) 0 i= -1/denominator d i := by
  have hd : denominator (falseData d gamma) i=denominator d i := rfl
  simp only [virtual,Pi.zero_apply,falseData_encoded,zero_sub,hd]

def normalizedVirtual (d : Data (K := K)) (gamma : K) (i : Fin 1048576) : K :=
  (gamma^26)⁻¹*virtual (falseData d gamma) 0 i

/-- Even with globally exact zero C1 and zero helper words, the actual OOD
interpolant produces this non-quadratic shift. It cannot be silently omitted
when importing the degree-two raw-helper recovery argument. -/
theorem source_no_quadratic (d : Data (K := K)) (i : Fin 1048576)
    (nonpole : denominator d i≠0) (p : K[X]) (degree : p.natDegree≤2)
    (G : Finset K) :
    (G.filter fun gamma => gamma≠0 ∧ p.eval gamma=normalizedVirtual d gamma i).card≤28 := by
  simp only [normalizedVirtual,falseData_virtual]
  exact inverse_shift_card (-1/denominator d i)
    (div_ne_zero (neg_ne_zero.mpr one_ne_zero) nonpole) p degree G

#print axioms cleared_nonzero
#print axioms cleared_degree
#print axioms inverse_shift_card
#print axioms falseData_checked
#print axioms falseData_batch
#print axioms falseData_interpolant
#print axioms falseData_encoded
#print axioms falseData_virtual
#print axioms source_no_quadratic
end
end AspisV8.QuotientHelperShift
